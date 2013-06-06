! Copyright (C) 2013 Gabriel Kerneis.
! Copyright (C) 2008 Doug Coleman.
! See http://factorcode.org/license.txt for BSD license.
USING: arrays grouping kernel math sequences byte-arrays
math.bitwise math.order math.parser locals literals typed
memory tools.time tools.profiler.sampling random fry prettyprint
math.statistics
;
EXCLUDE: math.bits => bits ;
IN: crypto.aes

CONSTANT: AES_BLOCK_SIZE 16

<< ! compile sbox at parse time for inv-sbox
CONSTANT: sbox
B{
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
}
>>

CONSTANT: inv-sbox
    $[ ${ 256 [ sbox index ] each-integer } >byte-array ]

CONSTANT: rcon
    $[
    { 0x01 0x02 0x04 0x08 0x10 0x20 0x40 0x80 0x1b 0x36 0x6c }
    [ 0 0 0 4byte-array ] map
    ]

! Arithmetic in GF(2^8) --- see FIPS 197, §4.
! a(x) and b(x) are represented by words.
! m(x) is fixed by the standard.

! See FIPS 197, §4.2.1.
TYPED: xtime ( b(x): fixnum -- x*b(x)%m(x): fixnum )
    [ 1 shift ]
    [ 0x80 bitand 0 = 0 0x1b ? ] bi bitxor 8 bits ; inline

! Accumulate x * ... * x * b(x).
TYPED: nxtimes ( b(x): fixnum n: fixnum -- seq: byte-array )
    [ [ xtime ] keep ] B{ } replicate-as nip ; inline

! See FIPS 197, §4.2.1.
! Almost symmetric, but more efficient if a(x) > b(x).
! Fails if b(x) = 0 (2map-reduce on an empty sequence).
TYPED: gf-mult ( a(x): fixnum b(x): fixnum -- a(x)*b(x)%m(x): fixnum )
    make-bits
    [ length nxtimes ] keep swap
    [ 0 ? ] [ bitxor ] 2map-reduce ; inline

! Words are represented as arrays of 4 bytes.
! A representation based on uint32 would certainly be more
! efficient, but [shift-rows] would need to be changed.

TYPED: sub-word ( word: byte-array -- word': byte-array )
    [ sbox nth ] map ;

TYPED: rot-word ( word: byte-array n: fixnum -- word': byte-array )
     cut-slice prepend ;

TYPED: xor-word ( word1: byte-array word2: byte-array -- word1^word2: byte-array )
    [ bitxor ] 2map ;

: expand-key-step ( key rcon -- next-key )
    over last 1 rot-word sub-word
    xor-word
    [ xor-word ] accumulate swap suffix rest ;

: aes-128-expand-key ( key -- round-keys )
    rcon swap [ expand-key-step ] accumulate nip ;

: sub-bytes ( state -- state' )
    [ sub-word ] map ;

: block-flip ( state -- state' )
    flip [ >byte-array ] map ;

: shift-rows ( state -- state' )
    block-flip [ rot-word ] map-index block-flip ;

TYPED: word-product ( word: byte-array word': byte-array -- byte: fixnum )
    [ gf-mult ] [ bitxor ] 2map-reduce ;

TYPED: matrix-product ( word: byte-array matrix -- word': byte-array )
    [ word-product ] with B{ } map-as ;

TYPED: mix-column ( word: byte-array -- word': byte-array )
    { B{ 2 3 1 1 }
      B{ 1 2 3 1 }
      B{ 1 1 2 3 }
      B{ 3 1 1 2 } } matrix-product ;

: mix-columns ( state -- state' )
    [ mix-column ] map ;

: add-round-key ( round-key state -- state' )
    [ xor-word ] 2map ;

: aes-round ( round-key state -- state' )
   sub-bytes shift-rows mix-columns add-round-key ;

: aes-128-encrypt ( expanded-key block -- encrypted-block )
    [ unclip ] dip add-round-key
    [ unclip-last swap ] dip
    [ swap aes-round ] reduce
    sub-bytes shift-rows add-round-key ;

! Inverse transformations for decrypt

: inv-shift-rows ( state -- state' )
    block-flip { 0 3 2 1 } [ rot-word ] 2map block-flip ;

: inv-sub-bytes ( state -- state' )
    [ [ inv-sbox nth ] map ] map ;

TYPED: inv-mix-column ( word: byte-array -- word': byte-array )
    { B{ 0xe 0xb 0xd 0x9 }
      B{ 0x9 0xe 0xb 0xd }
      B{ 0xd 0x9 0xe 0xb }
      B{ 0xb 0xd 0x9 0xe } } matrix-product ;

: inv-mix-columns ( state -- state' )
    [ inv-mix-column ] map ;

: inv-aes-round ( round-key state -- state' )
   inv-shift-rows inv-sub-bytes add-round-key inv-mix-columns ;

: aes-128-decrypt ( expanded-key block -- decrypted-block )
    [ reverse unclip ] dip add-round-key
    [ unclip-last swap ] dip
    [ swap inv-aes-round ] reduce
    inv-shift-rows inv-sub-bytes add-round-key ;

! Alternative implementation using OpenSSL
USING: openssl.libcrypto classes.struct ;

: openssl-expand-encrypt-key ( key -- round-keys )
    concat 128 AES_KEY <struct>
    [ AES_set_encrypt_key ] keep nip ; ! XXX check return value

: openssl-expand-decrypt-key ( key -- round-keys )
    concat 128 AES_KEY <struct>
    [ AES_set_decrypt_key ] keep nip ; ! XXX check return value

: openssl-encrypt ( expanded-key block -- decrypted-block )
    concat 16 <byte-array> rot [ AES_encrypt ] 2keep drop ;

: openssl-decrypt ( expanded-key block -- decrypted-block )
    concat 16 <byte-array> rot [ AES_decrypt ] 2keep drop ;

! Benchmarks and profiling

: random-block ( -- block )
    4 [ 4 random-bytes ] replicate ;

! Expand a random key only once, then apply aes-function to
! 1000 random blocks, and output the average speed.
:: aes-bench ( expand-function aes-function -- bench-quot )
    random-block expand-function call( k -- k' )
    '[ 1000
     [ _ random-block aes-function call( k b -- b' ) drop ]
     times
     ]
    gc ; inline

: time-bench ( expand-function aes-function -- block/s )
    aes-bench benchmark 1e12 swap / ;

: profile-bench ( expand-function aes-function -- )
    aes-bench profile top-down profile. ;

: run-bench ( -- )
    10 [ [ aes-128-expand-key ] [ aes-128-encrypt ]
    time-bench ] replicate mean >integer .
    10 [ [ aes-128-expand-key ] [ aes-128-decrypt ]
    time-bench ] replicate mean >integer . ;

: openssl-bench ( -- )
    [ openssl-expand-encrypt-key ] [ openssl-encrypt ]
    time-bench >integer .
    [ openssl-expand-decrypt-key ] [ openssl-decrypt ]
    time-bench >integer .  ;
