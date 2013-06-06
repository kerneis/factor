! Copyright (C) 2013 Gabriel Kerneis.
! Copyright (C) 2008 Doug Coleman.
! See http://factorcode.org/license.txt for BSD license.
USING: kernel sequences grouping tools.test crypto.aes
byte-arrays ;
IN: crypto.aes.tests

[ B{
    0x63 0x7c 0x77 0x7b 0xf2 0x6b 0x6f 0xc5
    0x30 0x01 0x67 0x2b 0xfe 0xd7 0xab 0x76
    0xca 0x82 0xc9 0x7d 0xfa 0x59 0x47 0xf0
    0xad 0xd4 0xa2 0xaf 0x9c 0xa4 0x72 0xc0
    0xb7 0xfd 0x93 0x26 0x36 0x3f 0xf7 0xcc
    0x34 0xa5 0xe5 0xf1 0x71 0xd8 0x31 0x15
    0x04 0xc7 0x23 0xc3 0x18 0x96 0x05 0x9a
    0x07 0x12 0x80 0xe2 0xeb 0x27 0xb2 0x75
    0x09 0x83 0x2c 0x1a 0x1b 0x6e 0x5a 0xa0
    0x52 0x3b 0xd6 0xb3 0x29 0xe3 0x2f 0x84
    0x53 0xd1 0x00 0xed 0x20 0xfc 0xb1 0x5b
    0x6a 0xcb 0xbe 0x39 0x4a 0x4c 0x58 0xcf
    0xd0 0xef 0xaa 0xfb 0x43 0x4d 0x33 0x85
    0x45 0xf9 0x02 0x7f 0x50 0x3c 0x9f 0xa8
    0x51 0xa3 0x40 0x8f 0x92 0x9d 0x38 0xf5
    0xbc 0xb6 0xda 0x21 0x10 0xff 0xf3 0xd2
    0xcd 0x0c 0x13 0xec 0x5f 0x97 0x44 0x17
    0xc4 0xa7 0x7e 0x3d 0x64 0x5d 0x19 0x73
    0x60 0x81 0x4f 0xdc 0x22 0x2a 0x90 0x88
    0x46 0xee 0xb8 0x14 0xde 0x5e 0x0b 0xdb
    0xe0 0x32 0x3a 0x0a 0x49 0x06 0x24 0x5c
    0xc2 0xd3 0xac 0x62 0x91 0x95 0xe4 0x79
    0xe7 0xc8 0x37 0x6d 0x8d 0xd5 0x4e 0xa9
    0x6c 0x56 0xf4 0xea 0x65 0x7a 0xae 0x08
    0xba 0x78 0x25 0x2e 0x1c 0xa6 0xb4 0xc6
    0xe8 0xdd 0x74 0x1f 0x4b 0xbd 0x8b 0x8a
    0x70 0x3e 0xb5 0x66 0x48 0x03 0xf6 0x0e
    0x61 0x35 0x57 0xb9 0x86 0xc1 0x1d 0x9e
    0xe1 0xf8 0x98 0x11 0x69 0xd9 0x8e 0x94
    0x9b 0x1e 0x87 0xe9 0xce 0x55 0x28 0xdf
    0x8c 0xa1 0x89 0x0d 0xbf 0xe6 0x42 0x68
    0x41 0x99 0x2d 0x0f 0xb0 0x54 0xbb 0x16
} ] [ sbox ] unit-test

[
B{
    0x52 0x09 0x6a 0xd5 0x30 0x36 0xa5 0x38 
    0xbf 0x40 0xa3 0x9e 0x81 0xf3 0xd7 0xfb 
    0x7c 0xe3 0x39 0x82 0x9b 0x2f 0xff 0x87 
    0x34 0x8e 0x43 0x44 0xc4 0xde 0xe9 0xcb 
    0x54 0x7b 0x94 0x32 0xa6 0xc2 0x23 0x3d 
    0xee 0x4c 0x95 0x0b 0x42 0xfa 0xc3 0x4e 
    0x08 0x2e 0xa1 0x66 0x28 0xd9 0x24 0xb2 
    0x76 0x5b 0xa2 0x49 0x6d 0x8b 0xd1 0x25 
    0x72 0xf8 0xf6 0x64 0x86 0x68 0x98 0x16 
    0xd4 0xa4 0x5c 0xcc 0x5d 0x65 0xb6 0x92 
    0x6c 0x70 0x48 0x50 0xfd 0xed 0xb9 0xda 
    0x5e 0x15 0x46 0x57 0xa7 0x8d 0x9d 0x84 
    0x90 0xd8 0xab 0x00 0x8c 0xbc 0xd3 0x0a 
    0xf7 0xe4 0x58 0x05 0xb8 0xb3 0x45 0x06 
    0xd0 0x2c 0x1e 0x8f 0xca 0x3f 0x0f 0x02 
    0xc1 0xaf 0xbd 0x03 0x01 0x13 0x8a 0x6b 
    0x3a 0x91 0x11 0x41 0x4f 0x67 0xdc 0xea 
    0x97 0xf2 0xcf 0xce 0xf0 0xb4 0xe6 0x73 
    0x96 0xac 0x74 0x22 0xe7 0xad 0x35 0x85 
    0xe2 0xf9 0x37 0xe8 0x1c 0x75 0xdf 0x6e 
    0x47 0xf1 0x1a 0x71 0x1d 0x29 0xc5 0x89 
    0x6f 0xb7 0x62 0x0e 0xaa 0x18 0xbe 0x1b 
    0xfc 0x56 0x3e 0x4b 0xc6 0xd2 0x79 0x20 
    0x9a 0xdb 0xc0 0xfe 0x78 0xcd 0x5a 0xf4 
    0x1f 0xdd 0xa8 0x33 0x88 0x07 0xc7 0x31 
    0xb1 0x12 0x10 0x59 0x27 0x80 0xec 0x5f 
    0x60 0x51 0x7f 0xa9 0x19 0xb5 0x4a 0x0d 
    0x2d 0xe5 0x7a 0x9f 0x93 0xc9 0x9c 0xef 
    0xa0 0xe0 0x3b 0x4d 0xae 0x2a 0xf5 0xb0 
    0xc8 0xeb 0xbb 0x3c 0x83 0x53 0x99 0x61 
    0x17 0x2b 0x04 0x7e 0xba 0x77 0xd6 0x26 
    0xe1 0x69 0x14 0x63 0x55 0x21 0x0c 0x7d 
}
] [ inv-sbox ] unit-test

! Check that rcon matches its theoretical definition
[ t ] [
    0x01 11 nxtimes
    rcon [ first ] map >byte-array
    = ] unit-test

! FIPS 197, §A.1
{
    {
    B{ 0x2b 0x7e 0x15 0x16 }
    B{ 0x28 0xae 0xd2 0xa6 }
    B{ 0xab 0xf7 0x15 0x88 }
    B{ 0x09 0xcf 0x4f 0x3c }
    B{ 0xa0 0xfa 0xfe 0x17 }
    B{ 0x88 0x54 0x2c 0xb1 }
    B{ 0x23 0xa3 0x39 0x39 }
    B{ 0x2a 0x6c 0x76 0x05 }
    B{ 0xf2 0xc2 0x95 0xf2 }
    B{ 0x7a 0x96 0xb9 0x43 }
    B{ 0x59 0x35 0x80 0x7a }
    B{ 0x73 0x59 0xf6 0x7f }
    B{ 0x3d 0x80 0x47 0x7d }
    B{ 0x47 0x16 0xfe 0x3e }
    B{ 0x1e 0x23 0x7e 0x44 }
    B{ 0x6d 0x7a 0x88 0x3b }
    B{ 0xef 0x44 0xa5 0x41 }
    B{ 0xa8 0x52 0x5b 0x7f }
    B{ 0xb6 0x71 0x25 0x3b }
    B{ 0xdb 0x0b 0xad 0x00 }
    B{ 0xd4 0xd1 0xc6 0xf8 }
    B{ 0x7c 0x83 0x9d 0x87 }
    B{ 0xca 0xf2 0xb8 0xbc }
    B{ 0x11 0xf9 0x15 0xbc }
    B{ 0x6d 0x88 0xa3 0x7a }
    B{ 0x11 0x0b 0x3e 0xfd }
    B{ 0xdb 0xf9 0x86 0x41 }
    B{ 0xca 0x00 0x93 0xfd }
    B{ 0x4e 0x54 0xf7 0x0e }
    B{ 0x5f 0x5f 0xc9 0xf3 }
    B{ 0x84 0xa6 0x4f 0xb2 }
    B{ 0x4e 0xa6 0xdc 0x4f }
    B{ 0xea 0xd2 0x73 0x21 }
    B{ 0xb5 0x8d 0xba 0xd2 }
    B{ 0x31 0x2b 0xf5 0x60 }
    B{ 0x7f 0x8d 0x29 0x2f }
    B{ 0xac 0x77 0x66 0xf3 }
    B{ 0x19 0xfa 0xdc 0x21 }
    B{ 0x28 0xd1 0x29 0x41 }
    B{ 0x57 0x5c 0x00 0x6e }
    B{ 0xd0 0x14 0xf9 0xa8 }
    B{ 0xc9 0xee 0x25 0x89 }
    B{ 0xe1 0x3f 0x0c 0xc8 }
    B{ 0xb6 0x63 0x0c 0xa6 }
    }
}
[
    {
    B{ 0x2b 0x7e 0x15 0x16 }
    B{ 0x28 0xae 0xd2 0xa6 }
    B{ 0xab 0xf7 0x15 0x88 }
    B{ 0x09 0xcf 0x4f 0x3c }
    } aes-128-expand-key concat
] unit-test

! FIPS 197, §4.2.1
{ 0xfe } [ 0x57 0x13 gf-mult ] unit-test

! Test vectors from wikipedia
! https://en.wikipedia.org/wiki/Rijndael_mix_columns
{ B{ 142 77 161 188 } } [ B{ 219 19 83 69 } mix-column ]
unit-test
{ B{ 159 220 88 157 } } [ B{ 242 10 34 92 } mix-column ]
unit-test
{ B{ 213 213 215 214 } } [ B{ 212 212 212 213 } mix-column ]
unit-test

! FIPS 197, §B

{
    {
    B{ 0x39 0x25 0x84 0x1d }
    B{ 0x02 0xdc 0x09 0xfb }
    B{ 0xdc 0x11 0x85 0x97 }
    B{ 0x19 0x6a 0x0b 0x32 }
    }
}
[
{
    B{ 0x2b 0x7e 0x15 0x16 }
    B{ 0x28 0xae 0xd2 0xa6 }
    B{ 0xab 0xf7 0x15 0x88 }
    B{ 0x09 0xcf 0x4f 0x3c }
} aes-128-expand-key
{
    B{ 0x32 0x43 0xf6 0xa8 }
    B{ 0x88 0x5a 0x30 0x8d }
    B{ 0x31 0x31 0x98 0xa2 }
    B{ 0xe0 0x37 0x07 0x34 }
}
aes-128-encrypt
] unit-test

{
{
    B{ 0x32 0x43 0xf6 0xa8 }
    B{ 0x88 0x5a 0x30 0x8d }
    B{ 0x31 0x31 0x98 0xa2 }
    B{ 0xe0 0x37 0x07 0x34 }
}
}
[
{
    B{ 0x2b 0x7e 0x15 0x16 }
    B{ 0x28 0xae 0xd2 0xa6 }
    B{ 0xab 0xf7 0x15 0x88 }
    B{ 0x09 0xcf 0x4f 0x3c }
} aes-128-expand-key
    {
    B{ 0x39 0x25 0x84 0x1d }
    B{ 0x02 0xdc 0x09 0xfb }
    B{ 0xdc 0x11 0x85 0x97 }
    B{ 0x19 0x6a 0x0b 0x32 }
    }
aes-128-decrypt
] unit-test

