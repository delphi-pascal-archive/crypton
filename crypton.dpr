(*************************************************************

CRYPTON 1.0 block cipher

Implemented in Pascal / Delphi by Alexander Myasnikow

Web: www.darksoftware.narod.ru

*************************************************************)

library crypton;

uses
  SysUtils;

type
  u32 = longword;
  u8  = byte;
  InKey = array [0..7] of u32;
  PInKey = ^InKey;
  EKey = array [0..7] of u32;
  PEKey = ^EKey;
  TLongWordArray = array [0..255] of longword;
  PLongwordArray = ^TLongWordArray;

var
  tab_gen: boolean = False;


const
  mb_0: u32 = $cffccffc;
  mb_1: u32 = $f33ff33f;
  mb_2: u32 = $fccffccf;
  mb_3: u32 = $3ff33ff3;
  mc0: u32  = $acacacac;
  mc1: u32  = $59595959;
  mc2: u32  = $b2b2b2b2;
  mc3: u32  = $65656565;

var
  p0:  array [0..15] of u8 = (15, 14, 10, 1, 11, 5, 8, 13, 9, 3, 2, 7, 0, 6, 4, 12);
  p1:  array [0..15] of u8 = (11, 10, 13, 7, 8, 14, 0, 5, 15, 6, 3, 4, 1, 9, 2, 12);
  ip0: array [0..15] of u8 = (12, 3, 10, 9, 14, 5, 13, 11, 6, 8, 2, 4, 15, 7, 1, 0);
  ip1: array [0..15] of u8 = (6, 12, 14, 10, 11, 7, 9, 3, 4, 13, 1, 0, 15, 2, 5, 8);

  s_box: array[0..3, 0..255] of u8;
  s_tab: array[0..3, 0..255] of u32;
  ce: array [0..51] of u32;
  cd: array [0..51] of u32;
  e_key: array [0..51] of u32;
  d_key: array  [0..51] of u32;

  function rotl (x: u32; v: u8): u32; stdcall;
    asm
        MOV CL, v
        MOV EAX, x
        ROL EAX, CL
    end;

  function rotr (x: u32; v: u8): u32; stdcall;
    asm
        MOV CL, v
        MOV EAX, x
        ROR EAX, CL
    end;


  function msk (n: u32): u32;
    begin
      Result := (($000000ff shr n) * $01010101);
    end;

  function brotl (x, n: u32): u32;
    begin
      Result := ((((x) and msk(n)) shl (n)) or (((x) and (not msk(n))) shr (8 - (n))));
    end;


  function __BYTE (x, n: u32): u8;
    begin
      Result := u8(x shr (8 * n));
    end;

  function row_perm (x: u32): u32;
    begin
      Result :=
        (x and mb_0) xor (rotl(x, 8) and mb_1) xor (rotl(x, 16) and mb_2) xor
        (rotl(x, 24) and mb_3);
    end;

  procedure fr0 (y: PLongWordArray; x: PLongWordArray; i: u32; k: u32);
    begin
      y^[i] := s_tab[i] [__BYTE(x^ [0], i)] xor s_tab[(i + 1) and 3]
        [__BYTE(x^ [1], i)] xor s_tab[(i + 2) and 3] [__BYTE(x^ [2], i)] xor
        s_tab[(i + 3) and 3] [__BYTE(x^ [3], i)] xor k;
    end;

  procedure fr1 (y: PLongWordArray; x: PLongWordArray; i: u32; k: u32);
    begin
      y^[i] := s_tab[(i + 2) and 3] [__BYTE(x^ [0], i)] xor
        s_tab[(i + 3) and 3] [__BYTE(x^ [1], i)] xor s_tab[i]
        [__BYTE(x^ [2], i)] xor s_tab[(i + 1) and 3] [__BYTE(x^ [3], i)] xor k;
    end;

  procedure f0_rnd (kp, b0, b1: PLongWordArray);
    begin
      fr0(b1, b0, 0, kp^ [0]);
      fr0(b1, b0, 1, kp^ [1]);
      fr0(b1, b0, 2, kp^ [2]);
      fr0(b1, b0, 3, kp^ [3]);
    end;

  procedure f1_rnd (kp, b0, b1: PLongWordArray);
    begin
      fr1(b0, b1, 0, kp^ [0]);
      fr1(b0, b1, 1, kp^ [1]);
      fr1(b0, b1, 2, kp^ [2]);
      fr1(b0, b1, 3, kp^ [3]);
    end;

  procedure gamma_tau (i: u32; b0, b1: PLongWordArray);
    begin
      b0^[i] := ((u32(s_box[(i + 2) and 3] [__BYTE(b1^ [0], i)])) or
        (u32(s_box[(i + 3) and 3] [__BYTE(b1^ [1], i)]) shl 8) or
        (u32(s_box[i] [__BYTE(b1^ [2], i)]) shl 16) or
        (u32(s_box[(i + 1) and 3] [__BYTE(b1^ [3], i)]) shl 24));
    end;


  procedure gen_tab ();
    var
      i, xl, xr, y, yl, yr, t: u32;
    begin

      for I := 0 to 255 do
        begin

        xl := p1[i shr 4];
        xr := p0[i and 15];

        yl := (xl and $0e) xor ((xl shl 3) and $08) xor ((xl shr 3) and $01) xor
          ((xr shl 1) and $0a) xor ((xr shl 2) and $04) xor
          ((xr shr 2) and $02) xor ((xr shr 1) and $01);

        yr := (xr and $0d) xor ((xr shl 1) and $04) xor ((xr shr 1) and $02) xor
          ((xl shr 1) and $05) xor ((xl shl 2) and $08) xor
          ((xl shl 1) and $02) xor ((xl shr 2) and $01);

        y := ip0[yl] or (ip1[yr] shl 4);

        yr := ((y shl 3) or (y shr 5)) and 255;
        xr := ((i shl 3) or (i shr 5)) and 255;
        yl := ((y shl 1) or (y shr 7)) and 255;
        xl := ((i shl 1) or (i shr 7)) and 255;

        s_box[0][i]  := u8(yl);
        s_box[1][i]  := u8(yr);
        s_box[2][xl] := u8(y);
        s_box[3][xr] := u8(y);

        s_tab[0][i]  := (yl * $01010101) and $3fcff3fc;
        s_tab[1][i]  := (yr * $01010101) and $fc3fcff3;
        s_tab[2][xl] := (y * $01010101) and $f3fc3fcf;
        s_tab[3][xr] := (y * $01010101) and $cff3fc3f;

        end;

      xl := $a54ff53a;

      for i := 0 to 12 do
        begin
        ce[4 * i + 0] := xl xor mc0;
        ce[4 * i + 1] := xl xor mc1;
        ce[4 * i + 2] := xl xor mc2;
        ce[4 * i + 3] := xl xor mc3;

        if (i and 1) > 0 then
          begin
          t := xl;
          end
        else
          begin
          t := rotr(xl, 16);
          end;

        yl := row_perm(t);

        cd[4 * (12 - i) + 0] := yl xor mc0;
        cd[4 * (12 - i) + 1] := rotl(yl, 24) xor mc1;
        cd[4 * (12 - i) + 2] := rotl(yl, 16) xor mc2;
        cd[4 * (12 - i) + 3] := rotl(yl, 8) xor mc3;

        xl := xl + $3c6ef372;
        end;
    end;


  procedure setup (in_key: PInKey); stdcall; export;
    var
      i, j, t0, t1: u32;
      tu: array[0..3] of u32;
      tv: array[0..3] of u32;
      ek: array[0..7] of u32;
      dk: array[0..7] of u32;

    begin

      if (not tab_gen) then
        begin
        gen_tab();
        tab_gen := True;
        end;

      tu[0] := 0;
      tv[0] := 0;
      tu[1] := 0;
      tv[1] := 0;
      tu[2] := 0;
      tv[2] := 0;
      tu[3] := 0;
      tv[3] := 0;

      tu[3] := __BYTE(in_key^ [6], 0) or (__BYTE(in_key^ [6], 2) shl 8) or
        (__BYTE(in_key^ [7], 0) shl 16) or (__BYTE(in_key^ [7], 2) shl 24);

      tv[3] := __BYTE(in_key^ [6], 1) or (__BYTE(in_key^ [6], 3) shl 8) or
        (__BYTE(in_key^ [7], 1) shl 16) or (__BYTE(in_key^ [7], 3) shl 24);

      tu[2] := __BYTE(in_key^ [4], 0) or (__BYTE(in_key^ [4], 2) shl 8) or
        (__BYTE(in_key^ [5], 0) shl 16) or (__BYTE(in_key^ [5], 2) shl 24);
      tv[2] := __BYTE(in_key^ [4], 1) or (__BYTE(in_key^ [4], 3) shl 8) or
        (__BYTE(in_key^ [5], 1) shl 16) or (__BYTE(in_key^ [5], 3) shl 24);

      tu[0] := __BYTE(in_key^ [0], 0) or (__BYTE(in_key^ [0], 2) shl 8) or
        (__BYTE(in_key^ [1], 0) shl 16) or (__BYTE(in_key^ [1], 2) shl 24);

      tv[0] := __BYTE(in_key^ [0], 1) or (__BYTE(in_key^ [0], 3) shl 8) or
        (__BYTE(in_key^ [1], 1) shl 16) or (__BYTE(in_key^ [1], 3) shl 24);

      tu[1] := __BYTE(in_key^ [2], 0) or (__BYTE(in_key^ [2], 2) shl 8) or
        (__BYTE(in_key^ [3], 0) shl 16) or (__BYTE(in_key^ [3], 2) shl 24);

      tv[1] := __BYTE(in_key^ [2], 1) or (__BYTE(in_key^ [2], 3) shl 8) or
        (__BYTE(in_key^ [3], 1) shl 16) or (__BYTE(in_key^ [3], 3) shl 24);


      fr0(@ek, @tu, 0, 0);
      fr0(@ek, @tu, 1, 0);
      fr0(@ek, @tu, 2, 0);
      fr0(@ek, @tu, 3, 0);
      fr1(@ek[4], @tv, 0, 0);
      fr1(@ek[4], @tv, 1, 0);
      fr1(@ek[4], @tv, 2, 0);
      fr1(@ek[4], @tv, 3, 0);

      t0 := ek[0] xor ek[1] xor ek[2] xor ek[3];
      t1 := ek[4] xor ek[5] xor ek[6] xor ek[7];

      ek[0] := ek[0] xor t1;
      ek[1] := ek[1] xor t1;
      ek[2] := ek[2] xor t1;
      ek[3] := ek[3] xor t1;
      ek[4] := ek[4] xor t0;
      ek[5] := ek[5] xor t0;
      ek[6] := ek[6] xor t0;
      ek[7] := ek[7] xor t0;

      d_key[48] := ek[0] xor ce[0];
      d_key[49] := ek[1] xor ce[1];
      d_key[50] := ek[2] xor ce[2];
      d_key[51] := ek[3] xor ce[3];

      dk[0] := brotl(row_perm(rotr(ek[2], 16)), 4);
      dk[1] := brotl(row_perm(rotr(ek[3], 24)), 2);
      dk[2] := row_perm(rotr(ek[0], 24));
      dk[3] := brotl(row_perm(ek[1]), 2);

      dk[4] := brotl(row_perm(ek[7]), 6);
      dk[5] := brotl(row_perm(rotr(ek[4], 24)), 6);
      dk[6] := brotl(row_perm(ek[5]), 4);
      dk[7] := brotl(row_perm(rotr(ek[6], 16)), 4);

      j := 0;
      for i := 0 to 12 do
        begin
        if (i and 1) > 0 then
          begin
          e_key[j] := ek[4] xor ce[j];
          e_key[j + 1] := ek[5] xor ce[j + 1];
          e_key[j + 2] := ek[6] xor ce[j + 2];
          e_key[j + 3] := ek[7] xor ce[j + 3];

          t1 := ek[7];
          ek[7] := rotl(ek[6], 16);
          ek[6] := rotl(ek[5], 8);
          ek[5] := brotl(ek[4], 2);
          ek[4] := brotl(t1, 2);
          end
        else
          begin
          e_key[j] := ek[0] xor ce[j];
          e_key[j + 1] := ek[1] xor ce[j + 1];
          e_key[j + 2] := ek[2] xor ce[j + 2];
          e_key[j + 3] := ek[3] xor ce[j + 3];

          t1 := ek[0];
          ek[0] := rotl(ek[1], 24);
          ek[1] := rotl(ek[2], 16);
          ek[2] := brotl(ek[3], 6);
          ek[3] := brotl(t1, 6);
          end;
        j := j + 4;
        end;

      j := 0;

      for i := 0 to 11 do
        begin

        if (i and 1) > 0 then
          begin

          d_key[j] := dk[4] xor cd[j];
          d_key[j + 1] := dk[5] xor cd[j + 1];
          d_key[j + 2] := dk[6] xor cd[j + 2];
          d_key[j + 3] := dk[7] xor cd[j + 3];

          t1 := dk[5];
          dk[5] := rotl(dk[6], 16);
          dk[6] := rotl(dk[7], 24);
          dk[7] := brotl(dk[4], 6);
          dk[4] := brotl(t1, 6);
          end
        else
          begin
          d_key[j] := dk[0] xor cd[j];
          d_key[j + 1] := dk[1] xor cd[j + 1];
          d_key[j + 2] := dk[2] xor cd[j + 2];
          d_key[j + 3] := dk[3] xor cd[j + 3];

          t1 := dk[2];
          dk[2] := rotl(dk[1], 8);
          dk[1] := rotl(dk[0], 16);
          dk[0] := brotl(dk[3], 2);
          dk[3] := brotl(t1, 2);
          end;
        j := j + 4;
        end;

      e_key[48] := row_perm(rotr(e_key[48], 16));
      e_key[49] := row_perm(rotr(e_key[49], 8));
      e_key[50] := row_perm(e_key[50]);
      e_key[51] := row_perm(rotr(e_key[51], 24));
    end;


  procedure crypt (in_blk: PLongWordArray); stdcall; export;
    var
      b0: array [0..3] of u32;
      b1: array [0..3] of u32;
    begin

      b0[0] := in_blk^ [0] xor e_key[0];
      b0[1] := in_blk^ [1] xor e_key[1];
      b0[2] := in_blk^ [2] xor e_key[2];
      b0[3] := in_blk^ [3] xor e_key[3];

      f0_rnd(@e_key[4], @b0, @b1);
      f1_rnd(@e_key[8], @b0, @b1);
      f0_rnd(@e_key[12], @b0, @b1);
      f1_rnd(@e_key[16], @b0, @b1);
      f0_rnd(@e_key[20], @b0, @b1);
      f1_rnd(@e_key[24], @b0, @b1);
      f0_rnd(@e_key[28], @b0, @b1);
      f1_rnd(@e_key[32], @b0, @b1);
      f0_rnd(@e_key[36], @b0, @b1);
      f1_rnd(@e_key[40], @b0, @b1);
      f0_rnd(@e_key[44], @b0, @b1);

      gamma_tau(0, @b0, @b1);
      gamma_tau(1, @b0, @b1);
      gamma_tau(2, @b0, @b1);
      gamma_tau(3, @b0, @b1);

      in_blk^[0] := b0[0] xor e_key[48];
      in_blk^[1] := b0[1] xor e_key[49];
      in_blk^[2] := b0[2] xor e_key[50];
      in_blk^[3] := b0[3] xor e_key[51];
    end;

  procedure decrypt (in_blk: PLongWordArray); stdcall; export;
    var
      b0: array [0..3] of u32;
      b1: array [0..3] of u32;
    begin

      b0[0] := in_blk^ [0] xor d_key[0];
      b0[1] := in_blk^ [1] xor d_key[1];
      b0[2] := in_blk^ [2] xor d_key[2];
      b0[3] := in_blk^ [3] xor d_key[3];

      f0_rnd(@d_key[4], @b0, @b1);
      f1_rnd(@d_key[8], @b0, @b1);
      f0_rnd(@d_key[12], @b0, @b1);
      f1_rnd(@d_key[16], @b0, @b1);
      f0_rnd(@d_key[20], @b0, @b1);
      f1_rnd(@d_key[24], @b0, @b1);
      f0_rnd(@d_key[28], @b0, @b1);
      f1_rnd(@d_key[32], @b0, @b1);
      f0_rnd(@d_key[36], @b0, @b1);
      f1_rnd(@d_key[40], @b0, @b1);
      f0_rnd(@d_key[44], @b0, @b1);

      gamma_tau(0, @b0, @b1);
      gamma_tau(1, @b0, @b1);
      gamma_tau(2, @b0, @b1);
      gamma_tau(3, @b0, @b1);

      in_blk^[0] := b0[0] xor d_key[48];
      in_blk^[1] := b0[1] xor d_key[49];
      in_blk^[2] := b0[2] xor d_key[50];
      in_blk^[3] := b0[3] xor d_key[51];
    end;


  function getblocksize (): u32; stdcall; export;
    begin
      Result := 128;
    end;

  function getkeysize (): u32; stdcall; export;
    begin
      Result := 256;
    end;

  procedure getciphername (p: PChar); stdcall; export;
    begin
      StrPCopy(p, 'CRYPTON-v1.0-256-PAS');
    end;


exports
  setup,
  crypt,
  decrypt,
  getciphername,
  getkeysize,
  getblocksize;

end.
