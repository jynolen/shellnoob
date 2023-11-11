#!/usr/bin/env python
# -*- coding: utf-8 -*-

# Copyright (c) 2013 Yanick Fratantonio
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
# THE SOFTWARE.

from ast import arg
from multiprocessing import Value
import os
import sys
import re
import stat
import io
import traceback
import shutil
from tempfile import mktemp, NamedTemporaryFile
from subprocess import call, Popen, PIPE
import binascii
from typing import Optional
import urllib
import urllib.request
import urllib.error
import argparse
from collections import namedtuple
from enum import StrEnum, auto
import logging

cbytes = lambda source, encoding='utf-8': bytes(source, encoding)
cstr = lambda source, encoding='utf-8': str(source, encoding)
urlread = lambda url: urllib.request.urlopen(url).read()
HTTPError = urllib.error.HTTPError

######################
### main functions ###
######################

class InputFormat(StrEnum):
    ASM = auto()
    OBJ = auto()
    BIN = auto()
    HEX = auto()
    C = auto()
    SHELLSTORM = auto()

class OutputFormat(StrEnum):
    ASM = auto()
    OBJ = auto()
    BIN = auto()
    HEX = auto()
    C = auto() 
    COMPLETEC = auto()
    PYTHON = auto()
    BASH = auto()
    RUBY = auto()
    PRETTY = auto()
    SAFEASM = auto()
    
class ShellNoobException(Exception):
    message: str
    def __init__(self, *args: object) -> None:
        super().__init__(*args)


class ShellNoob():

    # {kernel#hardware#flag_64_bit#flag_intel}
    objdump_options_map = {
        'Linux#i[2-6]?86#32#att' : '',
        'Linux#i[2-6]?86#32#intel' : '-m i386:intel',
        'Linux#x86_64#32#att' : '',
        'Linux#x86_64#32#intel' : '-m i386:intel',
        'Linux#x86_64#64#att' : '',
        'Linux#x86_64#64#intel' : '-m i386:x86-64:intel',
        'Linux#arm.*#32#.*' : '',
        'FreeBSD#i[2-6]?86#32#.*' : '',
        'FreeBSD#amd64#32#att' : ''
    }

    # {kernel-hardware-flag_64_bit-flag_intel}
    as_options_map = {
        'Linux#i[2-6]?86#32#att' : '',
        'Linux#i[2-6]?86#32#intel' : '-msyntax=intel -mnaked-reg',
        'Linux#x86_64#32#att' : '--32',
        'Linux#x86_64#32#intel' : '--32 -msyntax=intel -mnaked-reg',
        'Linux#x86_64#64#att' : '',
        'Linux#x86_64#64#intel' : '-msyntax=intel -mnaked-reg',
        'Linux#arm.*#32#.*' : '',
        'FreeBSD#i[2-6]?86#32#.*' : '',
        'FreeBSD#amd64#32#att' : ''
    }

    # {kernel-hardware-flag_64_bit-flag_intel}
    ld_options_map = {
        'Linux#i[2-6]?86#32#.*' : '',
        'Linux#x86_64#32#.*' : '-m elf_i386',
        'Linux#x86_64#64#.*' : '',
        'Linux#arm.*#32#.*' : '',
        'FreeBSD#i[2-6]?86#32#.*' : '-m elf_i386_fbsd',
        'FreeBSD#amd64#32#att' : '-m elf_i386_fbsd'
    }

    # {kernel-hardware-flag_64_bit-flag_intel}
    gcc_options_map = {
        'Linux#i[2-6]?86#32#.*' : '',
        'Linux#x86_64#32#.*' : '-m32',
        'Linux#x86_64#64#.*' : '',
        'Linux#arm.*#32#.*' : '',
        'FreeBSD#i[2-6]?86#32#.*' : '-m elf_i386_fbsd'
    }

    # {kernel-hardware}
    breakpoint_hex_map = {
        '.*#i[2-6]?86' : 'cc',
        '.*#x86_64' : 'cc'
    }

    # {kernel-hardware}
    comment_as_char = {
        '.*#i[2-6]?86' : '#',
        '.*#x86_64' : '#',
        '.*#arm.*' : '@',
    }

    # [hardware]
    hw_with_align = ['arm.*']

    shellcode_t = ('.section .text\n'
                   '%s\n'
                  )

    completec_t = (
'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <errno.h>
#include <malloc.h>

%s

int len = (sizeof(shellcode) > 2048) ?sizeof(shellcode):2048;

int main() {
    // make sure the memory is RWX to support self-modifying shellcode
    char *target = (char *) memalign(4096, len);
    mprotect(target, len, PROT_READ | PROT_WRITE | PROT_EXEC);
    memcpy(target, shellcode, len);
    (*(void (*)()) target)();
    return 0;
}
'''
)

    shellstorm_t = 'http://www.shell-storm.org/shellcode/files/shellcode-%s.php'


    def __init__(self, flag_64_bit=False, flag_intel=False, with_breakpoint=False, verbose=0, keep_files=False):
        self.shellnoob_fp = os.path.abspath(__file__)
        self.flag_64_bit = '64' if flag_64_bit else '32'
        self.flag_intel = 'intel' if flag_intel else 'att'
        self.with_breakpoint = with_breakpoint
        self.verbose = verbose
        self.debug = True if self.verbose >= 4 else False
        self.keep_files = keep_files
        self.kernel = self.get_kernel()
        self.hardware = self.get_hardware()
        self.set_conv_functions()
        self.check_compatibility()

    def set_conv_functions(self):
        for i in InputFormat:
            for o in OutputFormat:
                func_name = '%s_to_%s' % (i, o)
                logging.debug('Creating %s' % func_name)
                if i == o: continue

                if func_name not in ShellNoob.__dict__:
                    # conversion not implemented: let's go through hex
                    setattr(ShellNoob, func_name, self.gen_conv_function(i, o))

    def gen_conv_function(self, input_fmt, output_fmt):
        # generate on-the-fly a conversion function going through the "hex" format
        to_hex_func_name = '%s_to_hex' % input_fmt
        from_hex_func_name = 'hex_to_%s' % output_fmt
        to_hex = ShellNoob.__dict__[to_hex_func_name]
        from_hex = ShellNoob.__dict__[from_hex_func_name]

        def conv(self, input_s, with_breakpoint=False):
            _hex = to_hex(self, input_s, with_breakpoint)
            _output = from_hex(self, _hex)
            return _output

        return conv

    def check_compatibility(self):
        try:
            self.get_objdump_options()
        except ShellNoobException as e:
            logging.exception('ERROR: %s' % e.message)
            sys.exit(2)
        try:
            self.get_as_options()
        except ShellNoobException as e:
            logging.exception('ERROR: %s' % e.message)
            sys.exit(2)
        try:
            self.get_ld_options()
        except ShellNoobException as e:
            logging.exception('ERROR: %s' % e.message)
            sys.exit(2)
        if self.with_breakpoint:
            try:
                self.get_breakpoint_hex()
            except ShellNoobException as e:
                logging.exception('ERROR: %s' % e.message)
                sys.exit(2)

    def get_objdump_options(self, kernel=None, hardware=None, flag_64_bit=None, flag_intel=None):
        # use the passed settings, if specified
        kernel = kernel if kernel is not None else self.kernel
        hardware = hardware if hardware is not None else self.hardware
        flag_64_bit = flag_64_bit if flag_64_bit is not None else self.flag_64_bit
        flag_intel = flag_intel if flag_intel is not None else self.flag_intel

        for entry, options in self.objdump_options_map.items():
            e_kernel, e_hardware, e_64, e_intel = entry.split('#')
            if not re.search(e_kernel, kernel): continue
            if not re.search(e_hardware, hardware): continue
            if not re.search(e_64, flag_64_bit): continue
            if not re.search(e_intel, flag_intel): continue
            logging.debug('MATCH with %s ~> %s' % (entry, options))
            return options
        raise ShellNoobException('objdump_options not found for the current setup')

    def get_as_options(self, kernel=None, hardware=None, flag_64_bit=None, flag_intel=None):
        # use the passed settings, if specified
        kernel = kernel if kernel is not None else self.kernel
        hardware = hardware if hardware is not None else self.hardware
        flag_64_bit = flag_64_bit if flag_64_bit is not None else self.flag_64_bit
        flag_intel = flag_intel if flag_intel is not None else self.flag_intel

        for entry, options in self.as_options_map.items():
            e_kernel, e_hardware, e_64, e_intel = entry.split('#')
            if not re.search(e_kernel, kernel): continue
            if not re.search(e_hardware, hardware): continue
            if not re.search(e_64, flag_64_bit): continue
            if not re.search(e_intel, flag_intel): continue
            logging.debug('MATCH with %s ~> %s' % (entry, options))
            return options
        raise ShellNoobException('as_options not found for the current setup')

    def get_ld_options(self, kernel=None, hardware=None, flag_64_bit=None, flag_intel=None):
        # use the passed settings, if specified
        kernel = kernel if kernel is not None else self.kernel
        hardware = hardware if hardware is not None else self.hardware
        flag_64_bit = flag_64_bit if flag_64_bit is not None else self.flag_64_bit
        flag_intel = flag_intel if flag_intel is not None else self.flag_intel

        for entry, options in self.ld_options_map.items():
            e_kernel, e_hardware, e_64, e_intel = entry.split('#')
            if not re.search(e_kernel, kernel): continue
            if not re.search(e_hardware, hardware): continue
            if not re.search(e_64, flag_64_bit): continue
            if not re.search(e_intel, flag_intel): continue
            logging.debug('MATCH with %s ~> %s' % (entry, options))
            return options
        raise ShellNoobException('ld_options not found for the current setup')

    def get_gcc_options(self, kernel=None, hardware=None, flag_64_bit=None, flag_intel=None):
        # use the passed settings, if specified
        kernel = kernel if kernel is not None else self.kernel
        hardware = hardware if hardware is not None else self.hardware
        flag_64_bit = flag_64_bit if flag_64_bit is not None else self.flag_64_bit
        flag_intel = flag_intel if flag_intel is not None else self.flag_intel

        for entry, options in self.gcc_options_map.items():
            e_kernel, e_hardware, e_64, e_intel = entry.split('#')
            if not re.search(e_kernel, kernel): continue
            if not re.search(e_hardware, hardware): continue
            if not re.search(e_64, flag_64_bit): continue
            if not re.search(e_intel, flag_intel): continue
            logging.debug('MATCH with %s ~> %s' % (entry, options))
            return options
        raise ShellNoobException('gcc_options not found for the current setup')

    def get_breakpoint_hex(self, kernel=None, hardware=None):
        # use the passed settings, if specified
        kernel = kernel if kernel is not None else self.kernel
        hardware = hardware if hardware is not None else self.hardware

        for entry, _hex in self.breakpoint_hex_map.items():
            e_kernel, e_hardware = entry.split('#')
            if not re.search(e_kernel, kernel): continue
            if not re.search(e_hardware, hardware): continue
            logging.debug('MATCH with %s-%s ~> %s' % (e_kernel, e_hardware, _hex))
            return _hex
        raise ShellNoobException('the breakpoint feature is not supported in the current configuration')

    def get_comment_as_char(self, kernel=None, hardware=None):
        # use the passed settings, if specified
        kernel = kernel if kernel is not None else self.kernel
        hardware = hardware if hardware is not None else self.hardware
        for entry, comment_char in self.comment_as_char.items():
            e_kernel, e_hardware = entry.split('#')
            if not re.search(e_kernel, kernel): continue
            if not re.search(e_hardware, hardware): continue
            logging.debug('MATCH with %s ~> %s' % (entry, comment_char))
            return comment_char


    ######################
    # standalone plugins #
    ######################

    def do_resolve_syscall(self, syscall, kernel=None, hardware=None):
        global cstr
        kernel = kernel if kernel is not None else self.kernel
        hardware = hardware if hardware is not None else self.hardware

        if (kernel, hardware) == ('Linux', 'x86_64'):
            platforms = {'i386' : ['asm/unistd_32.h'],
                         'x86_64' : ['asm/unistd_64.h']
                        }
            symbol = '__NR_%s' % syscall
        else:
            platforms = {'i386' : ['sys/syscall.h']}
            symbol = 'SYS_%s' % syscall
        body = 'printf("%%d", %s); return 0;' % (symbol)

        for platform, includes in reversed(sorted(platforms.items())):
            try:
                tmp_exe_fp = self.include_and_body_to_exe_fp(includes, body)
            except ShellNoobException:
                logging.exception('ERROR: syscall %s not found for platform %s' % (syscall, platform))
                continue

            p = Popen(tmp_exe_fp, stdout=PIPE)
            output, error = p.communicate()
            retval = p.returncode
            if retval == 0:
                print('%s ~> %s' % (platform, cstr(output, "utf-8")))
            else:
                logging.error('ERROR: reval %s while resolving syscall %s' % (retval, syscall))
            if not self.keep_files:
                os.unlink(tmp_exe_fp)

    def do_resolve_const(self, const):
        includes = ['sys/types.h',
                    'sys/stat.h',
                    'sys/mman.h',
                    'fcntl.h',
                   ]
        body = 'printf("%%d", %s); return 0;' % (const)

        try:
            tmp_exe_fp = self.include_and_body_to_exe_fp(includes, body)
        except ShellNoobException:
            logging.error('constant %s not found' % const)
            return

        p = Popen(tmp_exe_fp, stdout=PIPE)
        output, error = p.communicate()
        retval = p.returncode
        if retval == 0:
            print('%s ~> %s' % (const, int(output)))
        else:
            logging.error('ERROR: reval %s while resolving const %s' % (retval, const))
        if not self.keep_files:
            os.unlink(tmp_exe_fp)

    def do_resolve_errno(self, errno):
        global cstr
        includes = ['string.h']

        body = 'printf("%%s", strerror(%s)); return 0;' % (errno)

        try:
            tmp_exe_fp = self.include_and_body_to_exe_fp(includes, body)
        except ShellNoobException:
            logging.exception('ERROR: errno %s not found' % errno)
            return

        p = Popen(tmp_exe_fp, stdout=PIPE)
        output, error = p.communicate()
        retval = p.returncode
        if retval == 0:
            print('%s ~> %s' % (errno, cstr(output, "utf-8")))
        else:
            logging.error('ERROR: reval %s while resolving errno %s' % (retval, errno))
        if not self.keep_files:
            os.unlink(tmp_exe_fp)

    def do_interactive_mode(self, asm_to_opcode_flag=None):
        global cbytes
        if asm_to_opcode_flag is None:
            print('asm_to_opcode (1) or opcode_to_asm (2)?: ', end='')
            answer = input()
            while answer != '1' and answer != '2':
                print('Choose between 1 and 2: ', end='')
                answer = input()
            asm_to_opcode_flag = True if answer == '1' else False
        assert asm_to_opcode_flag is not None
        if asm_to_opcode_flag:
            print('asm_to_opcode selected (type "quit" or ^C to end)')
            ins = ''
            quit = False
            while not quit:
                while not ins:
                    print('>> ', end='')
                    ins = input().strip(' \t\n')
                    if ins.lower() == 'quit':
                        quit = True
                if quit: continue
                try:
                    _hex = self.ins_to_hex(ins)
                    print('%s ~> %s' % (ins, _hex))
                except Exception as e:
                    logging.exception('ERROR: %s' % e)
                ins = ''
        else:
            print('opcode_to_asm selected (type "quit" or ^C to end)')
            _hex = ''
            quit = False
            while not quit:
                while not _hex:
                    print('>> ', end='')
                    _hex = input().strip(' \t\n')
                    if _hex.lower() == 'quit':
                        quit = True
                if quit: continue
                try:
                    _hex = _hex.replace(' ','').strip(' \t\n')
                    asm = self.hex_to_pretty(_hex)
                    print('%s ~> %s' % (cbytes(_hex), asm))
                except Exception as e:
                    logging.exception('ERROR: %s' % e)
                _hex = ''


    def do_conversion(self, input_fp, output_fp, input_fmt, output_fmt):
        global cbytes
        logging.info(f'Converting from {input_fp.name} ({input_fmt}) to {output_fp.name} ({output_fmt})')

        if input_fmt == 'shellstorm':
            _input = input_fp  # shellcode id
        else:
            _input = input_fp.read()

        conv_func_name = '%s_to_%s' % (input_fmt, output_fmt)
        try:
            _output = getattr(self, conv_func_name)(_input)
        except AttributeError as err:
            logging.exception('ERROR: conversion mode "%s" is not supported.' % conv_func_name)
            sys.exit(2)
        except ShellNoobException as err:
            logging.exception('%s' % err)
            sys.exit(2)

        if not isinstance(_output, bytes):
            _output = cbytes(_output)
        # writing the output
        output_fp.write(_output)

        if output_fmt == 'exe' and output_fp != '-':
            # chmod 700
            os.chmod(output_fp, stat.S_IRUSR | stat.S_IWUSR | stat.S_IXUSR)

    def do_strace(self, input_fp, input_fmt):
        logging.debug('IN do_strace')

        exe_fp = mktemp()

        self.do_conversion(input_fp, exe_fp, input_fmt, 'exe')

        p = Popen('strace %s' % exe_fp, shell=True)
        p.wait()

        if not self.keep_files:
            os.unlink(exe_fp)
        logging.debug('OUT do_strace')

    def do_gdb(self, input_fp, input_fmt):
        logging.debug('IN do_gdb')

        exe_fp = mktemp()

        self.do_conversion(input_fp, exe_fp, input_fmt, 'exe')

        start_addr = None
        try:
            start_addr = self.get_start_address(exe_fp)
        except:
            logging.exception('WARNING: failed to get the start address :-(')

        if start_addr:
            cmd = 'gdb -ex "break *%s" -q %s' % (start_addr, exe_fp)
        else:
            cmd = 'gdb -q %s' % exe_fp
        p = Popen(cmd, shell=True)
        p.wait()

        if not self.keep_files:
            os.unlink(exe_fp)

        logging.debug('OUT do_gdb')


    #############################
    # executable patching utils #
    #############################

    def get_bits(self, exe_fp):
        bits = None
        if '32-bit' in os.popen('file %s' % exe_fp).read():
            bits = 32
        elif '64-bit' in os.popen('file %s' % exe_fp).read():
            bits = 64
        assert bits is not None
        return bits

    def get_text_section_info(self, exe_fp):
        bits = self.get_bits(exe_fp)
        vm_address, file_offset, size = None, None, None
        lines = os.popen('readelf -S %s' % exe_fp).read().split('\n')
        if bits == 32:
            for line in lines:
                m = re.search(r'.text\s+\w+\s+([0-9a-f]+)\s+([0-9a-f]+)\s+([0-9a-f]+)', line)
                if not m: continue
                vm_address = int(m.group(1), 16)
                file_offset = int(m.group(2), 16)
                size = int(m.group(3), 16)
                break
        elif bits == 64:
            for line in lines:
                if vm_address is None and file_offset is None:
                    m = re.search(r'.text\s+\w+\s+([0-9a-f]+)\s+([0-9a-f]+)', line)
                    if not m: continue
                    vm_address = int(m.group(1), 16)
                    file_offset = int(m.group(2), 16)
                    continue
                else:
                    m = re.search(r'\s+([0-9a-f]+)\s+[0-9a-f]+', line)
                    if not m: raise Exception('error while parsing readelf -S (64bit)')
                    size = int(m.group(1), 16)
                    break
        else:
            raise Exception('weird number of bits')

        assert vm_address is not None and file_offset is not None and size is not None

        return vm_address, file_offset, size

    def get_file_offset_from_vm_address(self, exe_fp, vm_address):
        start_vm, start_file, size = self.get_text_section_info(exe_fp)
        assert start_vm <= vm_address <= start_vm + size
        return vm_address - start_vm + start_file

    def do_fork_nopper(self, exe_fp):
        lines = os.popen('objdump -d %s' % exe_fp).read().split('\n')
        for line in lines:
            logging.info(line)
            m = re.search(r'([0-9a-f]+):\s+[0-9a-f ]+\s+call.*fork', line)
            if not m: continue
            vm_address = int(m.group(1), 16)
            file_offset = self.get_file_offset_from_vm_address(exe_fp, vm_address)
            logging.debug('Found call to fork @ 0x%x (file offset 0x%x)' % (vm_address, file_offset))
            self.do_exe_patch(exe_fp, b'\x90\x90\x90\x31\xc0', file_offset)

    def do_exe_patch(self, exe_fp, data, file_offset=None, vm_address=None, replace=True):
        if not replace:
            raise Exception('unsupported')

        if file_offset is None and vm_address is None:
            raise Exception('you need to specify at least one of the two ;)')

        if file_offset is None:
            file_offset = self.get_file_offset_from_vm_address(exe_fp, vm_address)

        f = open(exe_fp, 'rb+')
        f.seek(file_offset)
        f.write(data)
        f.close()


    ###################
    ### conversions ###
    ###################

    def asm_to_hex(self, asm, with_breakpoint=None):
        global cstr
        logging.debug('IN asm_to_hex')
        with_breakpoint = with_breakpoint if with_breakpoint is not None else self.with_breakpoint
        obj = self.asm_to_obj(asm, with_breakpoint)
        _hex = self.obj_to_hex(obj, with_breakpoint=False)

        logging.debug('OUT asm_to_hex')
        return cstr(_hex)

    def bin_to_hex(self, _bin, with_breakpoint=None):
        global cbytes
        logging.debug('IN bin_to_hex')
        with_breakpoint = with_breakpoint if with_breakpoint is not None else self.with_breakpoint

        prepend = self.get_breakpoint_hex() if with_breakpoint else ''
        logging.debug('OUT bin_to_hex')
        return cbytes(prepend) + binascii.hexlify(_bin)

    def obj_to_hex(self, obj, with_breakpoint=None):
        logging.debug('IN obj_to_hex')
        with_breakpoint = with_breakpoint if with_breakpoint is not None else self.with_breakpoint

        tmp_obj_f = NamedTemporaryFile(delete=False)
        tmp_obj_fp = tmp_obj_f.name
        tmp_obj_f.write(obj)
        tmp_obj_f.close()

        tmp_bin_fp = mktemp()

        cmd = 'objcopy -O binary %s %s' % (tmp_obj_fp, tmp_bin_fp)
        retval = self.exec_cmd(cmd)
        try:
            assert retval == 0
        except:
            raise Exception('Error while converting from obj_to_hex. Not valid ELF?')

        _bin = open(tmp_bin_fp, 'rb').read()
        _hex = self.bin_to_hex(_bin, with_breakpoint)

        if not self.keep_files:
            os.unlink(tmp_obj_fp)
            os.unlink(tmp_bin_fp)

        logging.debug('OUT obj_to_hex')
        return _hex

    def c_to_hex(self, c, with_breakpoint=None):
        logging.debug('IN c_to_hex')
        with_breakpoint = with_breakpoint if with_breakpoint is not None else self.with_breakpoint

        logging.warning('c_to_hex just extracts the \\xXX looking parts. Check that everything it\'s fine!')

        def get_next_hex(buf):
            slash_x_idx = buf.find('\\x')
            if slash_x_idx == -1:
                return '', ''
            return buf[slash_x_idx+2:slash_x_idx+4], buf[slash_x_idx+4:]

        prepend = self.get_breakpoint_hex() if with_breakpoint else ''

        _hex = ''
        _next = c
        while _next:
            hex_byte, _next = get_next_hex(_next)
            _hex += hex_byte
        _hex = prepend + _hex

        logging.debug('OUT c_to_hex')
        return _hex

    def shellstorm_to_hex(self, shellstorm_id, with_breakpoint=None):
        global cstr, urlread
        logging.debug('IN shellstorm_to_hex')
        with_breakpoint = with_breakpoint if with_breakpoint is not None else self.with_breakpoint

        logging.warning('shellstorm_to_hex just extracts the \\xXX looking parts. Check that everything it\'s fine!')

        shellstorm_url = self.shellstorm_t % shellstorm_id
        try:
            content = cstr(urlread(shellstorm_url))
        except HTTPError as err:
            raise ShellNoobException('ERROR: failed fetching shellcode from %s (%s)' % (shellstorm_url, err))

        # prefilter some html stuff
        after_pre_idx = content.find('<pre>') + len('<pre>')
        before_body_idx = content.find('<body>')
        content = content[after_pre_idx:before_body_idx]

        _hex = self.c_to_hex(content, with_breakpoint)

        logging.debug('OUT shellstorm_to_hex')
        return _hex

    ################
    ### hex_to_* ###
    ################

    def hex_to_asm(self, _hex, with_breakpoint=None):
        logging.debug('IN hex_to_asm')
        with_breakpoint = with_breakpoint if with_breakpoint is not None else self.with_breakpoint

        obj = self.hex_to_obj(_hex, with_breakpoint)
        asm = self.obj_to_asm(obj, with_breakpoint=False)

        logging.debug('OUT hex_to_asm')
        return asm

    def hex_to_obj(self, _hex, with_breakpoint=None):
        logging.debug('IN hex_to_obj')
        with_breakpoint = with_breakpoint if with_breakpoint is not None else self.with_breakpoint

        if not isinstance(_hex, str):
            _hex = cstr(_hex)
        if len(_hex) != 0 and _hex.endswith('\n'):
            _hex = _hex.rstrip('\n')
            logging.warning('stripped a \'\\n\' at the end of the hex')
        if len(_hex) == 0 or len(_hex) % 2 != 0:
            raise Exception('Not valid _hex: %s' % _hex)

        prepend = self.get_breakpoint_hex() if with_breakpoint else ''
        _hex = prepend + _hex

        asm = self.hex_to_asm_bytes(_hex)
        obj = self.asm_to_obj(asm, with_breakpoint=False)

        logging.debug('OUT hex_to_obj')
        return obj

    def hex_to_exe(self, _hex, with_breakpoint=None):
        logging.debug('IN hex_to_exe')
        with_breakpoint = with_breakpoint if with_breakpoint is not None else self.with_breakpoint

        completec = self.hex_to_completec(_hex, with_breakpoint)
        exe = self.c_to_exe(completec, with_breakpoint=False)
        logging.debug('OUT hex_to_exe')
        return exe

    def hex_to_bin(self, _hex, with_breakpoint=None):
        global cstr
        logging.debug('IN hex_to_bin')
        with_breakpoint = with_breakpoint if with_breakpoint is not None else self.with_breakpoint

        if not isinstance(_hex, str):
            _hex = cstr(_hex)
        if len(_hex) != 0 and _hex.endswith('\n'):
            _hex = _hex.rstrip('\n')
            logging.warning('stripped a \'\\n\' at the end of the hex')
        if len(_hex) == 0 or len(_hex) % 2 != 0:
            raise Exception('Not valid _hex: %s' % _hex)

        prepend = self.get_breakpoint_hex() if with_breakpoint else ''
        _hex = prepend + _hex

        logging.debug('OUT hex_to_bin')
        return binascii.unhexlify(_hex)

    def hex_to_c(self, _hex, with_breakpoint=None):
        logging.debug('IN hex_to_c')
        with_breakpoint = with_breakpoint if with_breakpoint is not None else self.with_breakpoint

        if not isinstance(_hex, str):
            _hex = cstr(_hex)
        if len(_hex) != 0 and _hex.endswith('\n'):
            _hex = _hex.rstrip('\n')
            logging.warning('stripped a \'\\n\' at the end of the hex')
        if len(_hex) == 0 or len(_hex) % 2 != 0:
            raise Exception('Not valid _hex: %s' % _hex)

        prepend = self.get_breakpoint_hex() if with_breakpoint else ''
        _hex = prepend + _hex

        template = 'char shellcode[] = "%s";'
        content = ''
        for idx in range(0, len(_hex), 2):
            content += '\\x%s' % _hex[idx:idx+2]
        out = template % content
        logging.debug('OUT hex_to_c')
        return out

    def hex_to_python(self, _hex, with_breakpoint=None):
        global cstr
        logging.debug('IN hex_to_python')
        with_breakpoint = with_breakpoint if with_breakpoint is not None else self.with_breakpoint

        if not isinstance(_hex, str):
            _hex = cstr(_hex)
        if len(_hex) != 0 and _hex.endswith('\n'):
            _hex = _hex.rstrip('\n')
            logging.warning('stripped a \'\\n\' at the end of the hex')
        if len(_hex) == 0 or len(_hex) % 2 != 0:
            raise Exception('Not valid _hex: %s' % _hex)

        prepend = self.get_breakpoint_hex() if with_breakpoint else ''
        _hex = prepend + _hex

        template = '%s'
        content = ''
        for idx in range(0, len(_hex), 2):
            content += '\\x%s' % _hex[idx:idx+2]
        out = template % content

        logging.debug('OUT hex_to_python')
        return out

    def hex_to_bash(self, _hex, with_breakpoint=None):
        logging.debug('IN hex_to_bash')
        with_breakpoint = with_breakpoint if with_breakpoint is not None else self.with_breakpoint

        out = self.hex_to_python(_hex, with_breakpoint)

        logging.debug('OUT hex_to_bash')
        return out

    def hex_to_ruby(self, _hex, with_breakpoint=None):
        logging.debug('IN hex_to_ruby')
        with_breakpoint = with_breakpoint if with_breakpoint is not None else self.with_breakpoint

        raise ShellNoobException()

    def hex_to_pretty(self, _hex, with_breakpoint=None):
        logging.debug('IN hex_to_pretty')
        with_breakpoint = with_breakpoint if with_breakpoint is not None else self.with_breakpoint

        obj = self.hex_to_obj(_hex, with_breakpoint)
        exe = self.obj_to_pretty(obj, with_breakpoint=False)
        logging.debug('OUT hex_to_pretty')
        return exe

    def obj_to_pretty(self, obj, with_breakpoint=None):
        logging.debug('IN obj_to_pretty')
        with_breakpoint = with_breakpoint if with_breakpoint is not None else self.with_breakpoint

        if with_breakpoint:
            raise Exception('the with_breakpoint option is NOT supported in obj_to_exe')

        if self.need_to_align():
            _hex = self.obj_to_hex(obj)
            logging.debug('hex lenght: ',len(_hex))
            aligned_hex = self.align_hex(_hex)
            logging.debug('aligned hex lenght: ' , len(aligned_hex))
            if _hex != aligned_hex:
                obj = self.hex_to_obj(aligned_hex, with_breakpoint=False)

        tmp_obj_f = NamedTemporaryFile(delete=False)
        tmp_obj_fp = tmp_obj_f.name
        tmp_obj_f.write(obj)
        tmp_obj_f.close()

        tmp_pretty_fp = mktemp()

        objdump_options = self.get_objdump_options()
        cmd = 'objdump -d %s %s > %s' % (objdump_options,
                                         tmp_obj_fp,
                                         tmp_pretty_fp
                                        )
        self.exec_cmd(cmd, caller='obj_to_pretty')

        pretty = open(tmp_pretty_fp).read()

        started = False
        lines = []
        for line in pretty.split('\n'):
            if not started and 'Disassembly of section .text:' in line:
                started = True
            if not started: continue
            lines.append(line)
        pretty = '\n'.join(lines)

        if not self.keep_files:
            os.unlink(tmp_obj_fp)
            os.unlink(tmp_pretty_fp)

        logging.debug('OUT obj_to_pretty')
        return pretty


    #########################
    ### additional blocks ###
    #########################

    def asm_to_obj(self, asm, with_breakpoint=None):
        global cstr
        logging.debug('IN asm_to_obj')
        with_breakpoint = with_breakpoint if with_breakpoint is not None else self.with_breakpoint

        if isinstance(asm, bytes):
            asm = cstr(asm)
        prepend = self.hex_to_asm_bytes(self.get_breakpoint_hex()) if with_breakpoint else ''

        asm = prepend + asm + '\n'
        tmp_asm_f = NamedTemporaryFile(delete=False)
        tmp_asm_fp = tmp_asm_f.name
        tmp_asm_f.write(asm.encode("utf-8"))
        tmp_asm_f.close()

        tmp_obj_fp = mktemp()

        as_options = self.get_as_options()

        cmd = 'as %s -o %s %s' % (as_options, tmp_obj_fp, tmp_asm_fp)
        self.exec_cmd(cmd, caller='asm_to_obj')
        if not os.path.isfile(tmp_obj_fp):
            raise Exception("not valid shellcode (asm_to_obj)")

        # delete all the symbols
        cmd = 'strip %s' % tmp_obj_fp
        self.exec_cmd(cmd, caller='asm_to_obj')

        obj = open(tmp_obj_fp, 'rb').read()

        if not self.keep_files:
            os.unlink(tmp_asm_fp)
            os.unlink(tmp_obj_fp)

        logging.debug('OUT asm_to_obj')
        return obj

    def obj_to_asm(self, obj, with_breakpoint=None):
        logging.debug('IN obj_to_asm')
        with_breakpoint = with_breakpoint if with_breakpoint is not None else self.with_breakpoint

        if self.need_to_align():
            _hex = self.obj_to_hex(obj)
            aligned_hex = self.align_hex(_hex)
            if _hex != aligned_hex:
                obj = self.hex_to_obj(aligned_hex, with_breakpoint=False)

        tmp_obj_f = NamedTemporaryFile(delete=False)
        tmp_obj_fp = tmp_obj_f.name
        tmp_obj_f.write(obj)
        tmp_obj_f.close()

        objdump_options = self.get_objdump_options()
        cmd = 'objdump -d %s %s | tr -s " "' % (objdump_options,
                                    tmp_obj_fp,
                                   )
        logging.info('(obj_to_asm) Executing: %s' % cmd)
        obj_out = os.popen(cmd).read()
        lines = obj_out.split('\n')
        started = False
        comment_char = ""
        prepend = self.hex_to_asm_bytes(self.get_breakpoint_hex()) if with_breakpoint else ''

        out_lines = []
        max_asm_len, max_help_asm_len = 0, 0
        for line in lines:
            if not started and 'Disassembly of section .text:' in line:
                started = True
                continue
            if not started: continue

            comment_char = self.get_comment_as_char()

            # asm started
            m = re.search(r'[0-9a-f]+:\s+([0-9a-f ]+)\t(.*)$', line)
            if not m:
                continue
            _hex = m.group(1).replace(' ', '').strip(' \t\n')
            help_asm = self.hex_to_asm_bytes(_hex).rstrip('\n')
            try:
                _ascii = '.ascii "%s"' % _hex
                _ascii = _ascii.strip(' \t\n')
            except UnicodeDecodeError:
                _ascii = ''
            asm = m.group(2).strip(' \t\n')
            sc_idx = asm.find(';')
            if sc_idx != -1:
                asm = asm[:sc_idx]

            if len(asm) > max_asm_len:
                max_asm_len = len(asm)
            if len(help_asm) > max_help_asm_len:
                max_help_asm_len = len(help_asm)

            out_line = (asm, help_asm, _ascii)
            out_lines.append(out_line)

        out = prepend
        out_fmt = '  {:<%d}\t{:} {:<%d} {:} {:}\n' % (max_asm_len, max_help_asm_len)
        for (asm, help_asm, _ascii) in out_lines:
            out += out_fmt.format(asm, comment_char, help_asm, comment_char, _ascii)

        if not self.keep_files:
            os.unlink(tmp_obj_fp)

        shellcode = self.shellcode_t % out

        logging.debug('OUT obj_to_asm')
        return shellcode

    def asm_to_exe(self, asm, with_breakpoint=None):
        logging.debug('IN asm_to_exe')
        with_breakpoint = with_breakpoint if with_breakpoint is not None else self.with_breakpoint

        _hex = self.asm_to_hex(asm, with_breakpoint)
        exe = self.hex_to_exe(_hex, with_breakpoint=False)

        logging.debug('OUT asm_to_exe')
        return exe

    def obj_to_exe(self, obj, with_breakpoint=None):
        logging.debug('IN obj_to_exe')
        with_breakpoint = with_breakpoint if with_breakpoint is not None else self.with_breakpoint

        if with_breakpoint:
            raise Exception('the with_breakpoint option is NOT supported in obj_to_exe')

        tmp_obj_f = NamedTemporaryFile(delete=False)
        tmp_obj_fp = tmp_obj_f.name
        tmp_obj_f.write(obj)
        tmp_obj_f.close()

        tmp_exe_fp = mktemp()

        ld_options = self.get_ld_options()

        # note: ld -V to list all the emulations
        cmd = 'ld -N %s %s -o %s' % (ld_options, tmp_obj_fp, tmp_exe_fp)
        retval = self.exec_cmd(cmd, True, caller='obj_to_exe')

        exe = open(tmp_exe_fp, 'rb').read()

        if not self.keep_files:
            os.unlink(tmp_obj_fp)
            os.unlink(tmp_exe_fp)

        logging.debug('OUT obj_to_exe')
        return exe

    def hex_to_safeasm(self, _hex, with_breakpoint=None):
        global cstr
        logging.debug('IN hex_to_safeasm')
        with_breakpoint = with_breakpoint if with_breakpoint is not None else self.with_breakpoint

        if not isinstance(_hex, str):
            _hex = cstr(_hex)
        if len(_hex) != 0 and _hex.endswith('\n'):
            _hex = _hex.rstrip('\n')
            logging.warning('stripped a \'\\n\' at the end of the hex')
        if len(_hex) == 0 or len(_hex) % 2 != 0:
            raise Exception('Not valid _hex: %s' % _hex)

        prepend = self.get_breakpoint_hex() if with_breakpoint else ''
        _hex = prepend + _hex

        asm = self.hex_to_asm_bytes(_hex)
        shellcode = self.shellcode_t % asm

        logging.debug('OUT hex_to_safeasm')
        return shellcode

    def hex_to_completec(self, _hex, with_breakpoint=None):
        logging.debug('IN hex_to_completec')
        with_breakpoint = with_breakpoint if with_breakpoint is not None else self.with_breakpoint

        c = self.hex_to_c(_hex, with_breakpoint)
        completec = self.completec_t % c

        logging.debug('OUT hex_to_completec')
        return completec

    def c_to_exe(self, c, with_breakpoint=None):
        global cbytes
        # NOTE assumption: the input is "compileable C"
        logging.debug('IN c_to_exe')

        if with_breakpoint:
            raise Exception('the with_breakpoint option is NOT supported in c_to_exe')

        if not isinstance(c, bytes):
            c = cbytes(c)
        tmp_c_f = NamedTemporaryFile(suffix='.c', delete=False)
        tmp_c_fp = tmp_c_f.name
        tmp_c_f.write(c)
        tmp_c_f.close()

        tmp_exe_fp = mktemp()

        gcc_options = self.get_gcc_options()
        cmd = 'gcc %s -o %s %s' % (gcc_options, tmp_exe_fp, tmp_c_fp)
        retval = self.exec_cmd(cmd, True, caller='c_to_exe')

        exe = open(tmp_exe_fp, 'rb').read()

        if not self.keep_files:
            os.unlink(tmp_c_fp)
            os.unlink(tmp_exe_fp)

        logging.debug('OUT c_to_exe')
        return exe


    ########################
    # additional functions #
    ########################

    def ins_to_hex(self, ins):
        asm = self.inss_to_asm([ins])
        _hex = self.asm_to_hex(asm)
        return _hex

    def hex_to_inss(self, _hex):
        asm = self.hex_to_asm(_hex)
        inss = asm.split('\n')[1:]
        inss = filter(lambda i:i.strip(' \t'), inss)
        inss = map(lambda i:i.split('#')[0], inss)
        inss = map(lambda i:i.strip(' \t'), inss)
        return list(inss)

    def inss_to_asm(self, inss):
        out = '\n'.join(inss)
        shellcode = self.shellcode_t % out
        return shellcode

    def asm_to_inss(self, asm):
        inss = []
        for i in asm.split('\n'):
            i = i.strip(' \t\n')
            if not i: continue
            inss.append(i)
        return inss


    ###########
    # helpers #
    ###########

    def hex_to_asm_bytes(self, _hex):
        hex_list = ['0x%s' % _hex[i:i+2] for i in range(0, len(_hex), 2)]
        asm = '.byte ' + ','.join(hex_list) + '\n'
        return asm

    def include_and_body_to_exe_fp(self, includes, body):
        global cbytes
        std_includes = set(('stdio.h', 'stdlib.h', 'errno.h'))
        includes = set(includes)
        includes.update(std_includes)

        c_prog = ''
        for inc in includes:
            c_prog += '#include<%s>\n' % inc

        c_prog += 'int main() {\n'
        c_prog += body
        c_prog += '}\n'

        tmp_c_fp = mktemp() + '.c'
        tmp_exe_fp = mktemp()

        with open(tmp_c_fp, 'wb') as f:
            f.write(cbytes(c_prog))

        cmd = 'gcc %s -o %s' % (tmp_c_fp, tmp_exe_fp)
        retval = self.exec_cmd(cmd)
        if retval != 0:
            output = ''
            raise ShellNoobException()

        if not self.keep_files:
            os.unlink(tmp_c_fp)

        return tmp_exe_fp

    def get_start_address(self, exe_fp):
        cmd = 'objdump -f %s' % exe_fp
        p = Popen(cmd, shell=True, stdout=PIPE, stderr=PIPE)
        _out, _err = p.communicate()
        assert p.returncode == 0

        _out = cstr(_out)
        for line in _out.split('\n'):
            line = line.strip(' \t\n')
            m = re.search('^start address (0x[0-9a-f]+)$', line)
            if not m: continue
            start_addr = m.group(1)
            return start_addr

        raise Exception('start address not found for %s' % exe_fp)

    def exec_cmd(self, cmd, redirect_stderr=False, caller=None):
        logging.info('(exec_cmd: "%s") Executing: "%s"' % (caller, cmd))

        if redirect_stderr:
            with open('/dev/null', 'wb') as f:
                retval = call(cmd, stderr=f, shell=True)
        else:
            retval = call(cmd, shell=True)

        logging.info('(exec_cmd: "%s") Ret value: %s' % (caller, retval))
        return retval

    def do_objdump_switch(self):
        # do we need to invert the bytes from objdump?
        return self.get_hardware().startswith('arm')

    def switch_bytes(self, _hex):
        # input: a hex string, like 34ab01ac

        # group them by 2 chars
        _hex = [_hex[i:i+2] for i in range(0, len(_hex), 2)]
        # reverse the list
        _hex = list(reversed(_hex))
        # build a string
        _hex = ''.join(_hex)
        return _hex

    def need_to_align(self, hardware=None):
        # use the passed settings, if specified
        hardware = hardware if hardware is not None else self.hardware
        for e_hardware in self.hw_with_align:
            if not re.search(e_hardware, hardware): continue
            return True
        return False

    def align_hex(self, _hex):
        assert len(_hex) % 2 == 0
        if (len(_hex)/2) % 4 != 0:
            _hex = _hex + '00'*(4 - (int(len(_hex)/2) % 4))
        assert len(_hex) % 8 == 0
        return _hex


    @staticmethod
    def get_kernel():
        return os.popen('uname -s').read().strip()

    @staticmethod
    def get_hardware():
        return os.popen('uname -m').read().strip()

    @staticmethod
    def do_install(force=False):
        if os.getuid() != 0:
            logging.error('ERROR: I need root!')
            sys.exit(1)
        install_dir = '/usr/local/bin'
        shellnoob_fp = os.path.join(install_dir, 'snoob')
        print('This will copy shellnoob into %s' % shellnoob_fp)
        if not force:
            input('Press a key to proceed..')
        shutil.copyfile(__file__, shellnoob_fp)
        os.chmod(shellnoob_fp, stat.S_IRWXU | stat.S_IRWXG | stat.S_IROTH | stat.S_IXOTH)
        print('SUCCESS. "snoob -h" should display shellnoob\'s help')

    @staticmethod
    def do_uninstall(force=False):
        if os.getuid() != 0:
            logging.error('ERROR: I need root!')
            sys.exit(1)
        install_dir = '/usr/local/bin'
        shellnoob_fp = os.path.join(install_dir, 'snoob')
        print('This will delete shellnoob from %s' % shellnoob_fp)
        if not force:
            input('Press a key to proceed..')
        os.unlink(shellnoob_fp)


class FormatAction(argparse.Action):

    FormatValue = namedtuple("FormatValue", ["format", "value"])

    def __init__(self,format=None,**kwargs):
        self.format:Optional[OutputFormat] = format
        super(FormatAction, self).__init__(**kwargs)

    def __call__(self, parser, namespace, values: io.TextIOWrapper, option_string=None):
        if not self.format:
            try:
                self.format = OutputFormat(values.name.split(".")[-1].lower())
            except ValueError:
                raise Exception("Unsupported Format")
        setattr(namespace, self.dest, FormatAction.FormatValue(self.format, values))

class OptionalBoolean(argparse.Action):

    def __init__(self,
                 option_strings,
                 dest,
                 const=None,
                 default=None,
                 required=False,
                 help=None,
                 metavar=None):
        super(OptionalBoolean, self).__init__(
            option_strings=option_strings,
            dest=dest,
            nargs=0,
            const=const,
            default=default,
            required=required,
            help=help)

    def __call__(self, parser, namespace, values, option_string=None):
        setattr(namespace, self.dest, self.const if option_string else self.default)

def parser():
    parser = argparse.ArgumentParser()
    parser.add_argument("--install", dest="install", action="store_true",
                        help='this just copies the script in a convinient position')
    parser.add_argument("--uninstall", dest="uninstall", action="store_true",
                        help="this just undo the action command")
    parser.add_argument("--64", dest="is64", action="store_true",
                        help="64 bits mode, default: 32 bits")
    parser.add_argument("--intel", dest="isIntel", action="store_true",
                        help="intel syntax mode, default: att")
    parser.add_argument("--breakpoint","-c", dest="addBreakpoint", action="store_true",
                        help="prepend a breakpoint (Warning: only few platforms/OS are supported!)")
    parser.add_argument("--keepfiles", "-k", dest="keepFiles", action="store_true",
                        help="keep files after operations")
    parser.add_argument("--verbosity", "-v", action='count', default=0,
                        help='Verbosity (can be repeat 2 times)')
    parser.add_argument("--quiet", "-q", action="store_true",
                        help='Quite Mode')    

    parser.add_argument("--force", action="store_true",
                        help='Force mode for install and uninstall')    


    subparsers = parser.add_subparsers(dest="action")
    subparsers.default = 'cli'
    cli = subparsers.add_parser('cli', help="CLI Mode")
    from_format_group = cli.add_mutually_exclusive_group(required=True)
    for format in InputFormat:
        file_type = argparse.FileType("rb") if format != InputFormat.SHELLSTORM else str
        from_format_group.add_argument(f"--from-{format}",dest="input", action=FormatAction, format=format, type=file_type,
                                        help=f'{format} as input',)
    from_format_group.add_argument("--from",dest="input", action=FormatAction, type=argparse.FileType("rb"))

    to_format_group = cli.add_mutually_exclusive_group(required=True)
    for format in OutputFormat:
        file_type = argparse.FileType("wb") if format != InputFormat.SHELLSTORM else str        
        to_format_group.add_argument(f"--to-{format}",dest="output", action=FormatAction, format=format, type=file_type,
                                        help=f'{format} as output')   
    to_format_group.add_argument(f"--to-gdb",dest="output", action="store_const", const="gdb",
                                    help=f'compiles it & run gdb & set breakpoint on entrypoint.')   
    to_format_group.add_argument(f"--to-strace",dest="output", action="store_const", const="strace",
                                    help=f'compiles it & run strace.')   
    to_format_group.add_argument("--to",dest="output", action=FormatAction, type=argparse.FileType("wb"))


    
    interractive = subparsers.add_parser('interactive', help="Interractive Mode", argument_default=None)
    interractive_group = interractive.add_mutually_exclusive_group()
    interractive_group.add_argument("--to-opcode", dest='toOpcode', action=OptionalBoolean, const=True, default=None,
                       help="Take ASM as input and output opcode")
    interractive_group.add_argument("--to-asm", dest='toOpcode', action=OptionalBoolean, const=False, default=None,
                       help="Take OpCode as input and output ASM")

    constPlugin = subparsers.add_parser('get-const', help="Const Plugin")
    constPlugin.add_argument('const', action="store",
                             help="Const value to retreive ")

    sysnumPlugin = subparsers.add_parser('get-sysnum', help="Sysnum Plugin")
    sysnumPlugin.add_argument('sysnum', action="store",
                             help="Sysnum value to retreive ")

    errnoPlugin = subparsers.add_parser('get-errno', help="Errno Plugin")
    errnoPlugin.add_argument('errno', action="store",
                             help="Errno value to retreive ")
    
    filePatchPlugin = subparsers.add_parser('file-patch', help="File Patch Plugin")
    filePatchPlugin.add_argument('exe_fp', action="store",
                                 help="Executable to patch")
    filePatchPlugin.add_argument('file_offset', action="store",
                                 help="Offset to in file.")
    filePatchPlugin.add_argument('data', action="store", type=binascii.unhexlify,
                                 help="Data to put at offet (hexstr).")

    vmPatchPlugin = subparsers.add_parser('vm-patch', help="VM Patch Plugin")
    vmPatchPlugin.add_argument('exe_fp', action="store",
                               help="VM to patch")
    vmPatchPlugin.add_argument('vm_address', action="store",
                               help="Address to patch.")
    vmPatchPlugin.add_argument('data', action="store", type=binascii.unhexlify,
                               help="Data to put at offet (hexstr).")    

    forkNopPlugin = subparsers.add_parser('fork-nopper', help="Forkn Nopper Plugin - this nops out the calls to fork().")
    forkNopPlugin.add_argument('exe_fork', action="store",
                               help="Executable to patch")

    return parser.parse_args()

def new_main(args):
    loggingLevel = [logging.ERROR, logging.INFO, logging.DEBUG]
    logging.basicConfig(stream=sys.stderr, level=loggingLevel[args.verbosity])
    if args.install:
        ShellNoob.do_install(args.force)
        sys.exit(0)
    if args.uninstall:
        ShellNoob.do_uninstall(args.force)
        sys.exit(0)

    snoob = ShellNoob(args.is64, args.isIntel, args.addBreakpoint, args.verbosity, args.keepFiles)
    if args.action == "interractive":
        snoob.do_interactive_mode(args.toOpcode)
    elif args.action == "get-const":
        snoob.do_resolve_const(args.const)
    elif args.action == "get-sysnum":
        snoob.do_resolve_const(args.sysnum)
    elif args.action == "get-errno":
        snoob.do_resolve_const(args.errno)
    elif args.action == "file-patch":
        snoob.do_exe_patch(args.exe_fp, args.data, file_offset=args.file_offset)
    elif args.action == "vm-patch":
        snoob.do_exe_patch(args.exe_fp, args.data, vm_address=args.vm_address)
    elif args.action == "fork-nopper":
        snoob.do_fork_nopper(args.exe_fork)
    elif args.action == "cli":
        if args.output == "gdb":
            snoob.do_gdb(args.input.value, args.input.format)
        elif args.output == "strace":
            snoob.do_strace(args.input.value, args.input.format)          
        else:
            snoob.do_conversion(args.input.value, args.output.value, args.input.format, args.output.format)

if __name__== '__main__':
    new_main(parser())
