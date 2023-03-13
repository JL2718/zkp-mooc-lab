pragma circom 2.0.0;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////// Templates from the circomlib ////////////////////////////////
////////////////// Copy-pasted here for easy reference //////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

/*
 * Outputs `a` AND `b`
 */
template AND() {
    signal input a;
    signal input b;
    signal output out;

    out <== a*b;
}

/*
 * Outputs `a` OR `b`
 */
template OR() {
    signal input a;
    signal input b;
    signal output out;

    out <== a + b - a*b;
}

/*
 * `out` = `cond` ? `L` : `R`
 */
template IfThenElse() {
    signal input cond;
    signal input L;
    signal input R;
    signal output out;

    out <== cond * (L - R) + R;
}

/*
 * (`outL`, `outR`) = `sel` ? (`R`, `L`) : (`L`, `R`)
 */
template Switcher() {
    signal input sel;
    signal input L;
    signal input R;
    signal output outL;
    signal output outR;

    signal aux;

    aux <== (R-L)*sel;
    outL <==  aux + L;
    outR <== -aux + R;
}

/*
 * Decomposes `in` into `b` bits, given by `bits`.
 * Least significant bit in `bits[0]`.
 * Enforces that `in` is at most `b` bits long.
 */
template Num2Bits(b) {
    signal input in;
    signal output bits[b];
    //log("num2bits: in=",in);
    for (var i = 0; i < b; i++) {
        bits[i] <-- (in >> i) & 1;
        bits[i] * (1 - bits[i]) === 0;
    }
    var sum_of_bits = 0;
    for (var i = 0; i < b; i++) {
        sum_of_bits += (2 ** i) * bits[i];
    }
    sum_of_bits === in;
}

/*
 * Reconstructs `out` from `b` bits, given by `bits`.
 * Least significant bit in `bits[0]`.
 */
template Bits2Num(b) {
    signal input bits[b];
    signal output out;
    var lc = 0;

    for (var i = 0; i < b; i++) {
        lc += (bits[i] * (1 << i));
    }
    out <== lc;
}

/*
 * Checks if `in` is zero and returns the output in `out`.
 */
template IsZero() {
    signal input in;
    signal output out;

    signal inv;

    inv <-- in!=0 ? 1/in : 0;

    out <== -in*inv +1;
    in*out === 0;
}

/*
 * Checks if `in[0]` == `in[1]` and returns the output in `out`.
 */
template IsEqual() {
    signal input in[2];
    signal output out;

    component isz = IsZero();

    in[1] - in[0] ==> isz.in;

    isz.out ==> out;
}

/*
 * Checks if `in[0]` < `in[1]` and returns the output in `out`.
 */
template LessThan(n) {
    assert(n <= 252);
    signal input in[2];
    signal output out;

    component n2b = Num2Bits(n+1);

    n2b.in <== in[0]+ (1<<n) - in[1];

    out <== 1-n2b.bits[n];
}

/////////////////////////////////////////////////////////////////////////////////////
///////////////////////// Templates for this lab ////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

/*
 * Outputs `out` = 1 if `in` is at most `b` bits long, and 0 otherwise.
 */
template CheckBitLength(b) {
    assert(b < 254);
    signal input in;
    signal output out;

    // TODO
    log("CBL",b,in);
    signal bits[b];
    for (var i = 0; i < b; i++) {
        bits[i] <-- (in >> i) & 1;
        bits[i] * (1 - bits[i]) === 0;
    }
    var sum_of_bits = 0;
    for (var i = 0; i < b; i++) {
        sum_of_bits += (2 ** i) * bits[i];
    }
    component eq = IsEqual();
    eq.in[0] <== sum_of_bits;
    eq.in[1] <== in;
    out <== eq.out;
}

/*
 * Enforces the well-formedness of an exponent-mantissa pair (e, m), which is defined as follows:
 * if `e` is zero, then `m` must be zero
 * else, `e` must be at most `k` bits long, and `m` must be in the range [2^p, 2^p+1)
 */
template CheckWellFormedness(k, p) {
    signal input e;
    signal input m;

    // check if `e` is zero
    component is_e_zero = IsZero();
    is_e_zero.in <== e;

    // Case I: `e` is zero
    //// `m` must be zero
    component is_m_zero = IsZero();
    is_m_zero.in <== m;

    // Case II: `e` is nonzero
    //// `e` is `k` bits
    component check_e_bits = CheckBitLength(k);
    check_e_bits.in <== e;
    //// `m` is `p`+1 bits with the MSB equal to 1
    //// equivalent to check `m` - 2^`p` is in `p` bits
    component check_m_bits = CheckBitLength(p);
    check_m_bits.in <== m - (1 << p);

    // choose the right checks based on `is_e_zero`
    component if_else = IfThenElse();
    if_else.cond <== is_e_zero.out;
    if_else.L <== is_m_zero.out;
    //// check_m_bits.out * check_e_bits.out is equivalent to check_m_bits.out AND check_e_bits.out
    if_else.R <== check_m_bits.out * check_e_bits.out;

    // assert that those checks passed
    if_else.out === 1;
}

/*
 * Right-shifts `b`-bit long `x` by `shift` bits to output `y`, where `shift` is a public circuit parameter.
 */
template RightShift(b, shift) {
    assert(shift < b);
    signal input x;
    signal output y;

    // TODO
    component n2b = Num2Bits(b);
    n2b.in <== x;
    component b2n = Bits2Num(b-shift);
    for (var i=0;i<(b-shift);i++){
        b2n.bits[i] <== n2b.bits[i+shift];
    }
    y <== b2n.out;
}

/*
 * Rounds the input floating-point number and checks to ensure that rounding does not make the mantissa unnormalized.
 * Rounding is necessary to prevent the bitlength of the mantissa from growing with each successive operation.
 * The input is a normalized floating-point number (e, m) with precision `P`, where `e` is a `k`-bit exponent and `m` is a `P`+1-bit mantissa.
 * The output is a normalized floating-point number (e_out, m_out) representing the same value with a lower precision `p`.
 */
template RoundAndCheck(k, p, P) {
    signal input e;
    signal input m;
    signal output e_out;
    signal output m_out;
    assert(P > p);

    // check if no overflow occurs
    component if_no_overflow = LessThan(P+1);
    if_no_overflow.in[0] <== m;
    if_no_overflow.in[1] <== (1 << (P+1)) - (1 << (P-p-1));
    signal no_overflow <== if_no_overflow.out;

    var round_amt = P-p;
    // Case I: no overflow
    // compute (m + 2^{round_amt-1}) >> round_amt
    var m_prime = m + (1 << (round_amt-1));
    //// Although m_prime is P+1 bits long in no overflow case, it can be P+2 bits long
    //// in the overflow case and the constraints should not fail in either case
    component right_shift = RightShift(P+2, round_amt);
    right_shift.x <== m_prime;
    var m_out_1 = right_shift.y;
    var e_out_1 = e;

    // Case II: overflow
    var e_out_2 = e + 1;
    var m_out_2 = (1 << p);

    // select right output based on no_overflow
    component if_else[2];
    for (var i = 0; i < 2; i++) {
        if_else[i] = IfThenElse();
        if_else[i].cond <== no_overflow;
    }
    if_else[0].L <== e_out_1;
    if_else[0].R <== e_out_2;
    if_else[1].L <== m_out_1;
    if_else[1].R <== m_out_2;
    e_out <== if_else[0].out;
    m_out <== if_else[1].out;
}

// from https://github.com/tokamak-network/circom-ethereum-opcodes/blob/main/circuits/exp.circom
template Exp () {
    signal input b;
    signal input x;
    signal output out;

    assert(x <= 253); // 2^253 already overflows 253-bit unsigned integer; the possible maximum exponenet value is 252 
                      // Since 2**253 can be described inside the circom integer range(the circom prime number is larger than 2**253), we set 253 as maximum value for other usages(SAR, etc).

    var NUM_BITS = 8; // An exponent can be represented into 8 bits since it is 252 at max. 

    signal exp[NUM_BITS];
    signal inter[NUM_BITS];
    signal temp[NUM_BITS]; // Used to detour a non-quadratic constraint error.

    component num2Bits = Num2Bits(NUM_BITS);
    num2Bits.in <== x;

    exp[0] <== b;
    inter[0] <== 1;
    for (var i = 0; i < NUM_BITS; i++) {
        temp[i] <== num2Bits.bits[i] * exp[i] + (1 - num2Bits.bits[i]); // exponent_bin[i] == 1 ? 2^(i+1) : 1
        if (i < NUM_BITS - 1) {
            inter[i + 1] <== inter[i] * temp[i];
            exp[i + 1] <== exp[i] * exp[i];
        } else {
            out <== inter[i] * temp[i];
        }
    }
}


/*
 * Left-shifts `x` by `shift` bits to output `y`.
 * Enforces 0 <= `shift` < `shift_bound`.
 * If `skip_checks` = 1, then we don't care about the output and the `shift_bound` constraint is not enforced.
 */
template LeftShift(shift_bound) {
    signal input x;
    signal input shift;
    signal input skip_checks;
    signal output y;

    component exp = Exp();
    exp.b <== 2;
    exp.x <== shift;
    y <== x * exp.out;

    component lt = LessThan(8);
    lt.in[0] <== shift;
    lt.in[1] <== shift_bound;
    component ite = IfThenElse();
    ite.cond <== skip_checks;
    ite.L <== 1;
    ite.R <== lt.out;
    ite.out === 1;
}

/*
 * Find the Most-Significant Non-Zero Bit (MSNZB) of `in`, where `in` is assumed to be non-zero value of `b` bits.
 * Outputs the MSNZB as a one-hot vector `one_hot` of `b` bits, where `one_hot`[i] = 1 if MSNZB(`in`) = i and 0 otherwise.
 * The MSNZB is output as a one-hot vector to reduce the number of constraints in the subsequent `Normalize` template.
 * Enforces that `in` is non-zero as MSNZB(0) is undefined.
 * If `skip_checks` = 1, then we don't care about the output and the non-zero constraint is not enforced.
 */

function log2(a) {
    if (a==0) {
        return 0;
    }
    var n = 1;
    var r = 0;
    while (n<=a) {
        r++;
        n *= 2;
    }
    return r-1;
}

template Log2(){
    signal input in;
    signal output out;
    out <-- log2(in);
    component exp = Exp();
    exp.b <== 2;
    exp.x <== out;
    component lta = LessThan(252);
    lta.in[0] <== out;
    lta.in[1] <== exp.out;
    lta.out === 0;

    component ltb = LessThan(252);
    ltb.in[0] <== out;
    ltb.in[1] <== 2*exp.out;
    ltb.out === 1;
}

template MSNZB(b) {
    signal input in;
    signal input skip_checks;
    signal output one_hot[b];

    // TODO
    // form witness
    var x = log2(in);
    for (var i=0;i<b;i++){
        one_hot[i] <-- i == x ? 1:0;
    }

    // constrain nonzero
    component iz = IsZero();
    iz.in <== in;
    
    // constrain to a single item
    var s = 0;
    for(var i=0;i<b;i++){
        s+=one_hot[i];
        one_hot[i]*(1-one_hot[i])===0; // binary constraint
    }
    component eq = IsEqual();
    eq.in[0] <== s;
    eq.in[1] <== 1;

    
    // constrain to 2*v > in > v
    component b2n = Bits2Num(b);
    for( var i=0;i<b;i++){
        b2n.bits[i] <== one_hot[i];
    }
    component lta = LessThan(b);
    lta.in[0] <== b2n.out;
    lta.in[1] <== in+1;

    signal z <== b2n.out * 2;
    component ltb = LessThan(b);
    ltb.in[0] <== in;
    ltb.in[1] <== z;
    
    component ite = IfThenElse();
    ite.cond <== skip_checks;
    ite.L <== 3;
    ite.R <== eq.out + lta.out + ltb.out;
    ite.out === 3;
}

/*
 * Normalizes the input floating-point number.
 * The input is a floating-point number with a `k`-bit exponent `e` and a `P`+1-bit *unnormalized* mantissa `m` with precision `p`, where `m` is assumed to be non-zero.
 * The output is a floating-point number representing the same value with exponent `e_out` and a *normalized* mantissa `m_out` of `P`+1-bits and precision `P`.
 * Enforces that `m` is non-zero as a zero-value can not be normalized.
 * If `skip_checks` = 1, then we don't care about the output and the non-zero constraint is not enforced.
 */
template Normalize(k, p, P) {
    signal input e;
    signal input m;
    signal input skip_checks;
    signal output e_out;
    signal output m_out;
    assert(P > p);

    // TODO
    //var l = log2(m);
    //e_out <-- e+l-p;
    //m_out <-- m<<(P-l);

    component msb = MSNZB(P+1);
    msb.in <== m;
    msb.skip_checks <== skip_checks;

    var m_acc = 0 ;
    var e_acc = 0 ; 
    signal ma[P+1];
    signal ea[P+1];
    for(var i=0;i<P+1;i++){
        ma[i] <== m * msb.one_hot[i] * (1<<(P-i));
        ea[i] <== msb.one_hot[i] * (e+i-p);
        m_acc += ma[i];
        e_acc += ea[i];
    }
    m_out <== m_acc;
    e_out <== e_acc;
}

/*
 * Adds two floating-point numbers.
 * The inputs are normalized floating-point numbers with `k`-bit exponents `e` and `p`+1-bit mantissas `m` with scale `p`.
 * Does not assume that the inputs are well-formed and makes appropriate checks for the same.
 * The output is a normalized floating-point number with exponent `e_out` and mantissa `m_out` of `p`+1-bits and scale `p`.
 * Enforces that inputs are well-formed.
 */
template FloatAdd(k, p) {
    signal input e[2];
    signal input m[2];
    signal output e_out;
    signal output m_out;

    // TODO
    component cwf0 = CheckWellFormedness(k,p);
    component cwf1 = CheckWellFormedness(k,p);
    cwf0.e <== e[0];
    cwf0.m <== m[0];
    cwf1.e <== e[1];
    cwf1.m <== m[1];

    component lt = LessThan(k);
    lt.in[0] <== e[0];
    lt.in[1] <== e[1];
    component swe = Switcher();
    swe.sel <== lt.out;
    swe.L <== e[0];
    swe.R <== e[1];
    component swm = Switcher();
    swm.sel <== lt.out;
    swm.L <== m[0];
    swm.R <== m[1];
    log("larger",swe.outL,swm.outL);
    log("smaller",swe.outR,swm.outR);

    var d = swe.outL-swe.outR;
    log(d);
    component ltd = LessThan(k);
    ltd.in[0] <== p+1;
    ltd.in[1] <== d;
    log("ltd.out",ltd.out);

    component itd = IfThenElse();
    itd.cond <== ltd.out;
    itd.L <== 0;
    itd.R <== d;
    log("itd.out",itd.out);

    component shl = LeftShift(254);
    shl.x <== swm.outL;
    shl.shift <== itd.out;
    shl.skip_checks <== ltd.out; 
    log("shl.y",shl.y);

    component norm  = Normalize(k,p,2*p+1);
    norm.e <== swe.outR;
    norm.m <== swm.outR + shl.y;
    norm.skip_checks <== ltd.out;
    log("raw",norm.e,norm.m);
    log("normed",norm.e_out,norm.m_out);

    component rac = RoundAndCheck(k,p,2*p+1);
    rac.e <== norm.e_out;
    rac.m <== norm.m_out;
    log("rounded",rac.e_out,rac.m_out);

    component ite = IfThenElse();
    ite.cond <== ltd.out;
    ite.R <== rac.e_out;
    ite.L <== swe.outL;
    component itm = IfThenElse();
    itm.cond <== ltd.out;
    itm.R <== rac.m_out;
    itm.L <== swm.outL;

    e_out <== ite.out;
    m_out <== itm.out;
    log(e_out,m_out);

}
