Proof of Collatz conjecture with a computer scientific twist
============================================================
The repository contains a proposal to prove Collatz conjecture using bit patterns and by showing the change of magnitude of bit presentation of the number will eventually decrease towards one when calculation of f(n) is iterated repeadetly. 

16th of November 2025
by Sami Mäkinen <sami.o.makinen@gmail.com> 

**Important**: The proposal was posted to Reddit/Collatz at 22nd of Nov 2025 and after quick review a major defect was found from the proposal. I'm trying to fix the issue and repost the idea, if I success to fix it. The major issue is that I assumed calculation of 3n + 1 would lead to only magnitude increase by one, which can be easily shown that it can increase magnitude by two as well. I have also noticed that I've oversimplified the bit pattern multiplications and going through those carefully now. For now, I've worked with part a) of the third theorem in the proof and I think I've got it fixed. 

Collatz conjecture
------------------

For on any natural number n > 0,
 - if the number is even, divide it by two.
 - if the number is odd, triple it and add one.

Formally,

```math 
 f(n) =
  \begin{cases}
    n/2   & \quad \text{if } n \equiv 0 \pmod{2}\\
    3n+1  & \quad \text{if } n \equiv 1 \pmod{2}
  \end{cases}
```

When f(n) is applied to the result of previous f(n), i.e. f(f(n)) and continued repeatedly for any starting natural number n > 0, the sequence of operations will result to 1.

While the empirical studies have shown the conjecture most likely true, the conjecture stays unproven. While some trials have been made the conjecture still lacks widely accepted proof.

This paper proposes an other trial of proof of the Collatz conjecture. While the author sincerely believes the proof is valid, it requires validation and acceptance from scientific community. So, take this with a grain of salt.

The proposal of proof is published openly for criticism and inspection.

About the proof
---------------

The proof starts with presentation of the new algorithm which iterates the steps using binary operations and eventually reaches 1 for any given number.

The proof relies on the observation that magnitude of number's binary presentation (number of bits in presentation) may increase and decrease on iterations and after careful study, the magnitude will eventually decrease. Finally, the magnitude will reach 1 when f(n) = 1.

The proof consist of three theorems and each theorem is demonstrated to be true. 
- the algorithm calculates the f(n),
- the algorithm stops when result is 1 for any input n,
- the algorithm is decidable and stops for any input n. 

As a conclusion, the theorems form a proof of Collatz conjecture.

About the notation
------------------

A number presented in binary format is only 0s and 1s. Each bit n presents value $2^i$, i >= 0. If the bit is 0, the value of the bit is 0, otherwise $2^i$ where i is the position of the bit. The value is sum of the bit presentations. The rightmost bit at position 0 of the binary presentation is called lowest significant bit (LSB). The leftmost bit of the binary presentation is called highest significant (HSB) bit.

In the paper the numbers are natural numbers $n \in N (> 0)$ and the binary presentation do not have a sign bit nor decimal fraction bits.

To avoid confusion between different bases the binary number is prefixed with a b. For example b11 is three while 11 is eleven.

If binary number is odd, the LSB is one. If the LSB is 0, the number is even. The LSB presents 1 if the bit is set. The other bits present even values $2^i (i > 0)$.

The special symbol \* is used to present 0 or more bits in sequence. Thus, 1\* is sequence of zero or more ones.

The 01\* presents a sequence of bits where the 0 is followed by zero or more number of 1-bits. Similarly, 10\* presents a sequence of bits where the 1 is followed any number of 0-bits. The special symbol ? is used when the bit value is unknown. The ? can be either 0 or 1. The ?\* is sequence of any bits and has length of 0 or more.

```
If 0 is added to ? the result is ?.  
If 1 is added to ? the result is ??, because if ? is 0, the result is 01 and,
                                             if ? is 1, the result is 10.
If ? is added to ? the result is ??, because the choices are: 0+0 = 00, 0+1 = 01,
                                                              1+0 = 01, 1+1 = 10.  
If 0 is added to 1* the result is 1*.  
If 1 is added to 1* the result is 10*.  
If 0 is added to 10* the result is 10*.  
If 1 is added to 10* the result is 10*1.  
If ? is added to 1*, the result is 1?*. If ? is zero, 0 + 1* = 1*. If ? is one, 1+1* = 10*
If 0 is added to ?*, the result is ?*.
If 1 is added to ?*, the result is ??*. The adding of 1 will change the binary sequence but
                                        because we don't know how, the result is ?*.
					The ? in front emphasizes that adding one may carry over.
If ? is added to ?*, the result is ??*.	The ? in front emphasizes that adding one may carry over.
1+0+? = ??
1+1+? = 1?   | 10 + ? = 1?
1+?+? = ??   | 1+0+0=01, 1+0+1=10, 1+1+1=11
?+?+? = ??

b?* = b1?*     | The HSB is always 1.
```

If adding two bit patterns both containing ?* a care must be take to recognize potential carry of ? over to next bit.
In the paper the adding of two bit patterns occur in calculation of 3n = 2n + n.
So, the n is first shifted to the left and then added to the result. Now, if the pattern contains ?*, the position
of ?* changes after the shifting.

```
n = 1?*0
2n = 1?*00
```

If we add n to 2n, we expand ?* to have match ?* in the patterns:

```
  ? ? ? ? 0  0   carry
-----------------
    1 ? ? ?* 0 0      | = 2n
+     1 ? ?* ? 0      | = n
-----------------
  ? ? ? ? ?* ? 0      | = ?*0 = 1?*0, because HSB is always 1.

=> 3 * 1?*0 = 1?*0
```

The notation n >> x means that the bits of n are shifted to the right x times. This is equal to division of n by $2^x$.

  n >> x = n / $2^x$

Some remarks about division by two (shifting to the right by 1). Notice: this would lead to rounding down, if pattern presents odd number.

```
b1 >> 1 = b0
b1* >> 1 = b1*
b1*0 >> 1 = b1*
b? >> 1 = b0
b?* >> 1 = b?*
b?0 >> 1 = b?
b?*0 >> 1 = b?*
```

The notation n << x means that the bits of n are shifted to the left x times. This is equal to multiplication of n by $2^x$.

  n << x = n \* $2^x$

Some remarks about multiplication by two (shifting to the left by 1).

```
b1 << 1 = b10
b1* << 1 = b1*0.
b? << 1 = ?0.
b?* << 1 = ?*0.
```

The minimum length of the bit string needed to present a number in binary presentation is called magnitude of the binary number and marked with M. The right-most 0s are ignored when calculating the
magnitude. Thus, b000100 magnitude is 3 because the right-most three zeros are ignored.

The magnitude M of bit string n is |n|. Simply, M = |n| Some rules about magnitude of n:

```
|0| = 0
|1| = 1
|?| = 0 or 1
|0*| = 0
|10*| >= 1
|1*| >= 0
|1?*| >= 1
|1?* << 1| = |1?*| + 1
|1?* >> 1| = |1?*| - 1
```  

Insights of calculating f(n) with binary operations
---------------------------------------------------

The multiplication of binary number by two is equal to shifting the bits to the left towards highest significant bit. Equally the division of binary number is shifting the bits to the right towards least
significant bit. If the binary number is odd, then the division by two will be rounded down to closest natural number. In the Collatz sequence the division by two will occur only to even numbers, so there
will be no rounding down.

**Corollary:** The 3n will result to odd number, if the n is odd. This can be easily proved using binary numbers.

  3n <=> 2n + n

Let a be the binary pattern of n. Because n is odd the LSB is 1.

```
  a = b?*1
```

2n will result to ba0 = b?\*10, because of the shift left. By adding n will result to ?\*1, because LSB is set in n.

```
    ?*10
  +  ?*1
  ------
     ?*1
```

The f(n) contains adding one to 3n when n is odd. Now, that we know 3n is odd adding one will result to an even number.

```
     ?*1
  +    1
  ------
     ?*0
```

When adding one to a binary number, the one is added to LSB of the number. If the LSB is one, the sum of bits would be more than binary numbers can present, so the result is carried over to the next bit in the number. If the next bit is one as well, the result is carried to next bit and so on. We say the adding of one propagates towards HSB. The carrying stops to first zero bit in the number. If all bits are ones, the magnitude of the binary number increases with one bit and the HSB is one while other bits are zero. In other words,

**Corollary**: `1* + 1 = 10*`

**Corollary**: `M(1* + 1) = M(1*) + 1`

**Lemma**: `|n| <= |f(f(n))| <= |n| + 1, if n is odd`

Proof:

2n < 3n + 1 < 4n  with all n > 1
2n = n << 1   || M + 1
4n = n << 2   || M + 2

The boundaries of magnitude change on 3n + 1 are clearly  1 and 2.

To show that the change can be 2, let

```
n = b1*      || presents odd number with all bits set to 1

3n = 2n + n
   = b1*0 + b1*

Because b1* has same magnitude

   1111...11   carry
------------- 
   111....110
 +  111...111
-------------
  10111...101
```

The result pattern is b101*01 and

```
|b101*01| = |b1*| + 2
```

Let

```
n = b1*
```

Step 1:

```
f(b1*) = 3 * b1* + b1
       = b101*01 + b1  || M + 2, from multiplication as shown above
       = b101*10       || M + 0
```

Step 2:

```
f(b101*10) = b101*1     || M - 1, from division
```

Therefore,

```
|f(f(b1*))| = |b1*| + 1
```

**Lemma** |f(b11?*1)| = |b11?*1| + 2

Proof:

Assuming we want to minimize the change in the bit pattern, ?* should be all zeros.

Thus, let

```
n = b110*1
```

First, let's check the result of 3n:

```
3 * b110*1 = b110*1 << 1 + b110*1
           = b110*10 + b110*1
	   = b10010*11

  11         carry
-------------
  11000...010
 + 1100...001
-------------
 100100...011   || M + 2
```

Step 1:

```
f(b110*1) = 3 * b110*1 + 1
          = b10010*11 + 1  || M + 2, from multiplication, see above.
	  = b10010*101     || M + 0, adding does not propagate to HSB.
```

Therefore,

```
|f(b110*1)| = |b110*1| + 2
```

**Lemma** |f(b100?*1)| = |b100?*1| + 1

Proof:

From previous lemma the magnitude change by two will occur when ?\* == 11?\*.

Let
```
n = b10011?*1

f(b10011?*1) = 3 * b10011?*1 + 1
             = b11?*1 + 1          || M + 1, from multiplication, see below.
	     = b11?*0              || M + 0, from addition. Adding does not propagate to HSB,
	                              because b11?*11 contains 0, see below.

3n = 2n + n

  0 0 ? c ? ? 0   carry
-----------------
  1 0 0 1 1?* 1 0
+   1 0 0 1 1?* 1
-----------------
  1 1 a b ??*?* 1     | Notation lacks impressiveness, so using a, b and c to present bits a, b, and c.
                        Either a or b must be zero, depending if c is 0 or 1.
                        a = 0 and b = 1  if c = 0
                        a = 1 and b = 0  if c = 1
```

Therefore,

```
|f(b100?*1)| = |b100?*1| + 1
```

What about |f(b101?*1)|?

**Lemma**: |f(b101?*1)| = |b101?*1| + 1 or |b101?*1| + 2

Proof:

From previous lemma the magnitude change by two will occur when ?\* == 11?\*.

Let
```
n = b1011?*1

f(b1011?*1) = 3 * b1011?*1 + 1
            = b1000?*1 + 1     || M + 2, from multiplication
            = b1000?*          || M + 0, from addition. Adding does not propagate to HSB,
                                  because of 0s in b1000.

 1 1 1 1 ? ? 0   carry
----------------
   1 0 1 1?* 1 0
+    1 0 1 1?* 1
----------------
 1 0 0 0 ??*?* 1
```

From previous lemma the multiplication increases magnitude by one on the left of pattern b00.
From previous lemma the magnitude change by two will occur when ?\* == 11?\*.

Let

```
n = b1010011?*1

f(b1010011?*1) = 3 * b1010011?*1 + 1
               = b111110?*1 + 1         || M + 1, from multiplication, see below.
               = b111110?*              || M + 0, from addition. Adding does not propagate to HSB,
	                                 because of 0 in b111110?*.

           1 1 ? ?     carry
---------------------- 
   1 0 1 0 0 1 1?* 1 0
 +   1 0 1 0 0 1 1?* 1
----------------------
   1 1 1 1 1 0 ? ??* 1
```

Therefore,

```
|f(b101?*1)| = |b101?*1| + 2   if |3 * 1?*| = |1?*1| + 2, or
               |b101?*1| + 1   if |3 * 1?*| = |1?*1| + 1
```

Building the algorithm
-------------

The sole purpose of the algorithm is to help prove the conjecture. 

The algorithm treats even numbers by dividing the number by two as in f(n). If the result of division is still even, we continue dividing as long the result is not even. We say the result is collapsed to even and use notation C(n) where pattern of n is 1?\*10\*. After C(n) = C(1?\*10\*) = 1?\*1. In notation C(n, x), x is used to specify number of times the division occurs. For example C(b?\*00, 2) means that division is done twice and, thus, C(b?\*00, 2) = b?).

If the number is odd, the algorithm uses different step depending on the three lowest significant bits.  The three lowest bits are examined because we want to know whether the result is even or odd and, if the result can be collapsed. If the LSB is 1, the result is odd. If the LSB is 0, the result is even and can be divided by two.

When n is odd the format is 1?\*1. If considering the three least significant bits of an odd number, we have following choices:

  a) b001

  b) b011

  c) b101

  d) b111

Let's check what happens to these when f(n) is applied to a)-d).

a) The algorithm will halt for the result being one. If f(n) is applied to b001:

`f(b001) = 3 * b001 + 1 = b011 + 1 = b100`.

The result is even and can be shifted twice to get odd number b1. In other words, to result is same.

  `C(b100, 2) = b1`

If applied to a pattern of b1?\*001, the result would be

```
n = b1?\*001

f(b1?*001) = 3 * b1?*001 + 1
           = 3 * b1?*000 + 3 * b001 + 1
           = 3 * b1?*000 + b100
           = b110?*100`
```

and next steps would collapse it to b110?\*1. Then algorithm would pick one of a)-d) depending on last three bits of b??1.

b) `f(b011) = 3 * b011 + 1 = b1001 + 1 = b1010`. 

The result is even and can be shifted once to get odd number b101. From c), we can see that b101 applying f(n) to it will result to b1.
Notice, if the pattern is b1?\*011, adding one will propagate toward HSB and must be resolved as well.

c) `f(b101) = 3 * b101 + 1 = b1111 + 1 = b10000`. 

The result is even and can be shifted four times to get odd number = b1. Notice, if the pattern is b1?\*101, adding one will propagate toward HSB and must be resolved as well.

d) `f(b111) = 3 * b111 + 1 = b10101 + 1 = b10110`. 

The result is even and can be shifted once to get odd number n = b1011. The n can be split

Let
```
     n = b1011 = b1000 + b011
```

Step 1:

```
  f(n) = 3n + 1
       = 3 * (b1000 + b011) + 1 
       = 3 * b1000 + 3 * b011 + 1 
       = 3 * b1000 + b1010
       = b100010
```

Step 2

```
  f(b100010) = b10001
```

Step 3:

```
  f(b10001) = 3 * b10000 + 3 * b001 + 1 
            = b110000 + b110
            = b110110
```

Step 4:

```
  f(b110110) = b11011
```

Notice, if the pattern is b1?\*111, adding one will propagate toward HSB and must be resolved as well.

The algorithm
----------------------

Let n be any positive natural number.

```
1  while( n > 1 ) {
2
3     // f(n) in case the n is even
4     if( ! (n & 1) ) {
5       n >>= 1; // div by 2
6       continue
7     }
8
9     // split n to first three bits and the rest
10    a = n & b111; // a three LSB's of n
11    r = n - a; // n = n - a + a
12    if( a == b001 ) {
13      // 3n + 1 = 3 * (n - a + a) + 1 = 3*r + 3a + 1
14      // 3*r + 3* b001 + 1 = 3*r +  b011 + 1 = 3*r + b100
15      n = 3*r + b100
16      //n >>= 2; // optimization possible      
17    }
18    else if( a == b011 ) {
19      // 3n + 1 = 3 * (n - a + a) + 1 = 3*r + 3a + 1
20      // 3*r + 3 * b011 + 1 = 3*r + b1001 + 1 = 3*r + b1010
21      n = 3*r + b1010 // adding probagates
22      //n >>= 1 // optimization possible      
23    }
24    else if( a == b101 ) {
25      // 3n + 1 = 3 * (n - a + a) + 1 = 3*r + 3a + 1
26      // 3*r + 3* b101 + 1 = 3*r + b1111 + 1 = 3*r + b10000
27      // b101 * 3 + 1 = b1111 + 1 = b10000. This is a hard case because, adding will probagate.
28      n = 3*r + b10000 // from probagation
29      // Notice, the n's three LSBs are 0, i.e. [?*]00b.
30      //n >>= 3 // optimization possible      
31    }
32    else if( a == b111) {
33      // 3n + 1 = 3 * (n - a + a) + 1 = 3*r + 3a + 1
34      // 3*r + 3* b111 + 1 = 3*r + b10101 + 1 = 3*r + b10110
35      n = 3*r + b10110 // from result. The adding probagates
36      //n >>= 1 // optimization possible      
37    }
38  }
```

Theorem 1 of the proof: Algorithm calculates f(n)
-------------------------

$f(n) = n/2    \quad \text{if } n \equiv 0 \pmod{2}$

In lines 4-6: If the given number n is even, the number is divided by two.

$f(n) = 3n+1  \quad \text{if } n \equiv 1 \pmod{2}$

In lines 10-1: n is split to higher and lower parts

```
  r is higher parts
  a is lower parts

  n = n - a + a
  r = n - a => n = r + a

  3n + 1 = 3 * (n - a + a) + 1
         = 3 * (r + a) + 1
         = 3r + 3a + 1
```

In lines 12-16: If a is 1 (b001)

```
        a = b001

  3n + 1 = 3r + 3a + 1 
         = 3r + 3 + 1
         = 3r + 4           || 4 is b100
```

In lines 18-22: If a is 3 (b011)

```
       a = b011
       
  3n + 1 = 3r + 3a + 1
         = 3r + 9 + 1
         = 3r + 10          || 10 is b1010
```

In lines 24-30: If a is 5 (b101)

```
       a = b101
       
  3n + 1 = 3r + 3a + 1
         = 3r + 15 + 1
         = 3r + 16          || 16 is b10000
```

In lines 32-36: If a is 7 (b111)

```
       a = b111
      
  3n + 1 = 3r + 3a + 1
         = 3r + 21 + 1
         = 3r + 22           || 22 is b10110
```

Theorem 2 of the proof: The algorithm will stop when result is 1 for any input n
--------------------------------------------------------------------------

From lines 1, 5, 15, 21, 28, 35: The algorithm loops and sets n = f(n) in every loop, until n == 1, when the iteration stops.

Theorem 3 of the proof: The algorithm will stop for any input n
--------------------------------------------------------

The proof relies on the observation that magnitude of n may increase and decrease on iterations and after careful study, the magnitude will eventually decrease. Finally, the magnitude will reach 1 when n = 1.

The idea is to show how bit string's length increases or decreases depending on lowest three bits when f(n) is applied to the number. Three bits helps to examine the changes in the number while the rest of the number is more or less anonymous patterns of bits. In the proposition the examination of changes in bit patterns form implicitly of state machine, because starting from one of the four introduced bit patterns, the stepping leads to an other start pattern or to 1. To make the idea work, the proposition should show that the length of bit strings will eventually decrease and reach 1.

When algorithm calculates and sets n=f(n), the magnitude of n changes. If n is even, the magnitude decreases by one because of division by two. If n is odd, the magnitude increases by one or two (lemma XX). 

Each of the three-bit patterns a)-d) are examined separately and shown that after various number of steps the magnitude of n will decrease. In each case, we need to go through two main cases where n is odd and magnitude increases by one or by two. The main cases have bit patterns 100?*??1 and 11?*??1. The lowest three bits may be b001, b011, b101, and b111.

```
|f(b100?*??1)| = |b100?*??1| + 1
|f(b101?*1)|   = |b101?*1| + 1 or |b101?*1| + 2
|f(b11?*??1)|  = |b11?*??1| + 2
```

a) with a = b001, we must consider two cases where multiplication increases |n| a.i) by one and a.ii) by two.

a.i) **Lemma**: |f(f(f(n)))| = |n| - 1, if n=b100?\*001 

Proof:

3\*n will increase the magnitude by one, but adding one does not. The addition will touch only the lowest three bits. Therefore, magnitude will remain the same or get smaller.

```
  n = b100?*001
  M = |n|
```

Step 1: 

```
  f(n) = f(b100?*001) = 3 * b100?*001 + 1
       = 3 * b100?*000 + b100
       = b11?*000 + b100               || M + 1, from multiplication
       = b11?*100                      || M + 0, from addition

       ? c ? 0  0 0 0 0   carry
----------------------
   1 0 0 ? ? ?* 0 0 0 0
     1 0 0 ? ?* ? 0 0 0
----------------------
   1 1 a b ? ?* ? 0 0 0            || a = ?, b = ?
                                      if c = 0, a = 0 and b = 1
                                      if c = 1, a = 1 and b = 0
   
```

Steps 2-3: 

```
  f(b11?*100) = b11?*10            || M - 1, from division
  f(b11?*10) = b11?*1              || M - 1, from division
```

Therefore,

`  |f(f(f(b10?*001)))| = |b10?*001| - 1`.

If n=b101?*001 with an assumption that the multiplication increases magnitude only by one, the magnitude decreases by one.

Let

```
n=b101?*001
```

Step 1:

```
f(b101?*001) = 3* b101?*001 + 1
             = b1111?*000 + b100   || M + 1, from multiplication, see below.
	     = b1111?*100

    0 0 0 0 ?  0 0 0  carry   | from assumption
 -------------------  
  1 0 1 0 ?* 0 0 0 0
+   1 0 1 ?* ? 0 0 0
 -------------------
  1 1 1 1 ?* ? 0 0 0 = 1111?*000

```

Step 2-3:

```
f(f(b1111?*100)) = b1111?*1        || M - 2, from division
```

a.ii) **Lemma**: |f(f(f(n)))| = |n|, if a.ii.a) n=b11?\*001 or a.ii.b) n = b101?\*001. In the case a.ii.b) with an assume the multiplication increases magnitude by two.

a.ii.a)

```
  n = b11?*001
  M = |b11?*001|
```

Step 1: 

```
  f(n) = f(b11?*001) = 3 * b11?*001 + 1
       = 3 * b11?*000 + b100
       = b10?*000 + b100             || M + 2, from multiplication
       = b10?*100                    || M + 0, from addition

   1 ? ? 0  0 0 0   carry
-------------------
   1 1 ? ?* 0 0 0 0
+    1 1 ?* ? 0 0 0
-------------------
 1 0 ? ? ?* ? 0 0 0   = 10?*000
```

Step 2: 

`  f(b10?*100) = b10?*10          || M - 1, from division`

Step 3: 

`  f(b10?*10) = b10?*1            || M - 1, from division`

Therefore,

`  |f(f(f(b11?*001)))| = |b11?*001|`.


In case of a.ii.a) the magnitude does not change and there is a risk the algorithm would not stop and loop for eternity.
From above we notice that f(f(f(b11?*001))) = b10?*1. The bit pattern has changed while the magnitude is still equal. Assume the lowest three bits are b001 after f(f(f(n). Because the highest two bits are now b10, the next step to be applied is either a.i) and magnitude decreases by one, or a.ii.b). 



Let

```
n = b10?*001
```

Step 1:

```
f(b10?*001) = 3 * b10?*001 + 1
            = 3 * b10?*000 + b100
            = b110110?*000 + b100          || M + 1, from multiplication
            = b110110?*100                 || M + 0, from addition

 ? ? ? ?             carry
--------------------
   1 0 ?  ?* 0 0 0 0
 +   1 0  ?* ? 0 0 0
--------------------
 ? ? ? ?  ?  ? 0 0 0
    
```

Steps 2-3:

```
f(f(b110110?*100)) = b110110?*1               || M-2, from division 
```

Therefore,

```
|f(f(f(f(f(f(n))))))| = |n| - 1, if n=b11?\*001 and f(f(f(n))) = b10010?*001.
```

a.ii.b) If n = b101?*001 and the multiplication increases magnitude by two.

Let

```
n = b101?*001
M = |n|
```

Step 1:

```
f(b101?*001) = 3 * b101?*1 + 1
             = 3 * b101?*000 + b100
	     = 1000?*000 + b100   || M + 2, from assumption. See below.
	     = 1000?*100          || M + 0, from addition


  1 1 1 ? 0  0 0 0 0  carry   | from assumption
 -------------------  
  1 0 1 ? ?* 0 0 0 0
+   1 0 1 ?* ? 0 0 0
 -------------------
1 0 0 0 ? ?* ? 0 0 0 = 1000?*000

```

Steps 2-3:

```
f(f(1000?*100)) = 1000?*1       || M-2, from division 
```

Therefore, 

`  |f(f(f(b101?*001)))| = |b101?*001|`.

In case of a.ii.b) the magnitude does not change and there is a risk the algorithm would not stop and loop for eternity.
From above we notice that f(f(f(b101?*001))) = b1000?*1. The bit pattern has changed while the magnitude is still equal. Assume the lowest three bits are b001 after f(f(f(n). Because the highest two bits are now b100, the next step to be applied is a.i) magnitude decreases by one.

### CONTINUE FROM HERE!!!

b) with a = b011, there is three scenarios to be considered:
  b.i) the multiplication increases |n| by one and addition increases magnitude by one.
  b.ii) the multiplication increases |n| by one and addition does not increase magnitude,
  b.iii) the multiplication increases |n| by two.
  
b.i) The case when the multiplication increases n by one and addition increases magnitude by one.

**Lemma**: If the fourth bit of the result of multiplication of r is set, the addition propagates and M increases by one only if all bits are set after the 3rd bit.  

Proof:

In other words, the addition of one increases M by 1, iff 3r = b1\*000.

Let

```
  n = 10?*011              || the highest bits are b10 because of assumption the multiplication won't increase the magnitude.
  M = |10?*011|
  3r = b1*000
```

and 

```
  f(n) = f(b10?*011) = b10?*011 * 3 + 1
       = 3r + b1010                 || r = b10?*000
       = b1*000 + b1010             || M + 1, from multiplication
       = b10*010                    || M + 1, from addition

  => |f(b10?*011)| = |b10?*011| + 2
```

If 3r is not b1\*000, the bit pattern of 3r will contain at least one 0 before HSB. Even if the there is only one zero, the propagation of addition of one will stop.

Let

```
  n = b10?*011
  3r = b1*01*000
```

and 

```
  f(n) = f(b10?*011) = b10?*011 * 3 + 1
       = 3r + b1010
       = b1*01*000 + b1010          || M + 1, from multiplication
       = b1*10*010                  || M + 0, from addition
```

Therefore,

```
  |f(b10?*011)| = |b10?*011| + 2  if 3r = b1*000
  |f(b10?*011)| = |b10?*011| + 1  if 3r = b1*01*000
```

In b.i) let's assume the addition of one increases by one. Thus, 3r=b1*000.

Step 1:

```
  n = b10?*011
  M = |n|
  3r = b1*000

  f(b10?*011) = b10*010    || M+2, see above
```

Step 2: 

`  f(b10*010) = b10*01  || M - 1, from division`

Step 3: 

`  see a.i)               || M - 1`


After division the result is b10\*001, and again this pattern leads to magnitude decrease due the a = b001.  The step 3 will result to same pattern b10\*001 but with one 0 less. This will repeat until the pattern is b101 which is shown to be 1 after some more iterations.

Therefore, in case of a = b011 when addition will propagate, the magnitude of n will start decreasing after third iteration and end to 1.

b.ii) The case when the multiplication increases n by one and addition does not increase magnitude,

**Lemma**: `|f(f(b10?*011))| = |b10?*011|, if adding does not propagate.`

Proof:

The result is `f(b10?*011) = 3*r + b1010`. If fourth bit of the 3\*r is not set, the magnitude won't change due adding 1.

Let 

```
   n = b10?*011
  3r = b110?*0000   || 4th bit not set after multiplication`
```

Step 1: 

```
  f(n) = f(b10?*011) = b10?*011 * 3 + 1
       = 3r + b1010                     || r = b10?*000
       = b110?*0000 + b1010             || M + 1, from multiplication
       = b110?*1010                     || M + 0, from addition
```

Step 2:  

```
  f(b110?*1010) = b?*101                || M - 1, from division
```

Therefore,

`  |f(f(b?*011))| = |b?*011|, if 3r = b?*0000 in the first step.`


The `f(f(b10?*011)) = b110?*101` and magnitude stays same. From c) we can see that next step reduces the magnitude.

The zero bit does not need to be 4th bit. The result is same if the zero bit is anywhere in the 3\*r result.

**Lemma**: If 3\*r is not b1\*000, the magnitude won't change due adding one. The propagation of addition stops at first zero bit. 

Proof:

In that case 3\*r is b11?\*01\*000.

Let

```
          n = b10?*101
        3*r = b11?*01*000

  f(b10?*101) = 3*r + b1010
              = b11?*01*000` + b1010      || M + 1, from multiplication
              = b11?*10*010               || M + 0, from addition
```

Step 2:

```
  f(b?*10*010) = b?*10*01                 || M - 1, from division
```

Therefore,

```
  |f(f(b10?*101))| = |b10?*101|  if 3r = b11?*01*000 in the first step.
```

b.iii) the case when the multiplication increases |n| by two

Let 

```
   n = b11?*011
   M = |n|
```

Step 1:

```
 f(b11?*011) = 3r + b1010            || r = b11?*000
             = 3 * b11?*000 + b1010
	     = b1001?*000 + b1010    || M + 2, from multiplication
	     = b10?*010              || M + 0, from addition. The addition cannot propagate to
                                               HSB because at least one zero in 3r.
```

Step 2:

```
f(b10?*010) = b10?*01               || M - 1, from division
```

If third lowest bit in b10?*01 is 0 (a=b001), the algorithm continues from a.i) and magnitude decreases.

If third lowest bit in b10?*01 is 1 (a=b101), the algorithm continues from c.i) or c.ii) and magnitude decreases.

c) with a = b101, we need to consider three cases
  c.i) the multiplication increases |n| by one and addition increases magnitude by one.
  c.ii) the multiplication increases |n| by one and addition does not increase magnitude,
  c.iii) the multiplication increases |n| by two,

c.i) **Lemma**: `|f(f(3n+1))| <= |n| - 2, if n=10?*101`

Proof:

Let

```
  n=b10?*101
```

Step 1:

```
  f(n)=f(b10?*101) = 3r + b10000
      = 3 * b10?*000 + b10000   
      = b110?*000 + b10000                || M + 1, from multiplication
      = b11?*000                          || M + 0, from addition. The addition cannot propagate to
                                                    HSB because at least one zero in 3r.
```

Steps 2-4:

```
  f(b11?*000) = b11?*00     || M-1, from division 
  f(b11?*00) = b11?*0       || M-1, from division 
  f(b11?*0) = b11?*         || M-1, from division

=> M+1-1-1-1 = M-2 
```

c.ii) the case when the multiplication increases n by one and addition does not increase magnitude,

The adding of one will increase magnitude, if 3r = b1\*?000. This would lead to following pattern:

Let

```
n = b10?*101
M = |n|
3r = b1*?000
```

Step 1:
```
f(n) = f(b10?*101)
     = 3r + b10000
     = b1*?000 + b10000  || M + 1, from multiplication
     = b10*?000          || M + 1, from addition
```

Steps 2-4:

```
f(f(f(b10*?000))) =  b10*?  || M-3, from division
```

We notice that if lowest ? is 0, the division continues and after the collapse C(10*) the result is b1 and magnitude is 1. The algorithm stops.
If lowest ? is 1, |f(f(f(f(b10?*101))))| = |b10?*101| - 1.

c.iii) the case when the multiplication increases n by two,

**Lemma**: |f(f(f(f(b11?*101))))| = |b11?*101| - 1

Proof:

Let

```
  n=b11?*101
```

Step 1:

```
  f(n)=f(b11?*101) = 3r + b10000
      = 3 * b11?*000 + b10000   
      = b1001?*000 + b10000               || M + 2, from multiplication
      = b10?*000                          || M + 0, from addition. The addition cannot propagate to
                                                    HSB because at least one zero in 3r.
```

Steps 2-4:

```
f(f(f(b10?*000))) =  b10?*  || M-3, from division
```

Notice, if the lowest ? is 0, the next step is division and magnitude decreases by one more.

Therefore,

```
|f(f(f(f(b11?*101))))| = |b11?*101| - 1
```

d) with a = b111 , we need to consider three cases
  d.i) the multiplication increases |n| by one and addition increases magnitude by one.
  d.ii) the multiplication increases |n| by one and addition does not increase magnitude,
  d.iii) the multiplication increases |n| by two,


d.i) **Lemma**: `|f(f(n))| = |n|, if n=b10?*111.`

Proof:

Let

```
n = b10?*111
M = |n|
```

Step 1:

```
f(b10?*111) = 3r + b10110           || r = b10?*000
            = 3 * b10?*000 + b10110
            = b110?*000 + b10110    || M + 1, from multiplication
      	    = b11?*110              || M + 0, from addition. The addition cannot propagate to
                                       HSB because the third highest bit is zero even if ?* == 1*.
```

Step 2:

```
f(f(b10?*111)) = f(b11?*110)
               = b11?*11            || M - 1, from division
```

Therefore,

`|f(f(b10?*111))| = |b10?*111|.

The result of d.i) is `f(f(b10?*111)) = b11?*11`. 

d.i.a) If third lowest bit in result is 0 (a=011), the pattern is b11?\*011 and the next step is b.iii).

d.i.b) If third lowest bit in result is   (a=111), the pattern is b11?\*111 and the next step is d.iii).


####
**Lemma** Magnitude decreases by one after applying f(n) seven times to b110?\*1111.

Proof:

Let

```
  n = b110?*1111
  M = |n|
```

Step 1:

```
  f(b110?*1111) = 3r + b10110
                = 3 * b110?*1000 + b10110
                = b10010?*11000 + b10110      || M + 2, from multiplication
                = b10010?*01110               || M + 0, from addition
#                = b10010?*01110 + b100000    || M + 0, from addition
```

Step 2:

```
  f(f(b11?*1111)) = f(b10010?*01110)
                  = b10010?*0111              || M - 1, from division
```

Step 3:

```
  f(f(f(b?*1111))) = f(b10010?*0111)
                   = 3 * b10010?*0000 + b10000
		   = b110110?*0000 + b10000   || M + 2, from multiplication
		   = b11011?*0000             || M + 0, from addition. The addition cannot propagate to
                                                 HSB because at least one zero in 3r.
```

Steps 4-7:

```
C(b11011?*0000, 4) = b11011?*                || M - 4
```

Therefore,

Magnitude decreases by one after applying f(n) seven times to b110?\*1111.

#####


d.ii) the case when the multiplication increases |n| by one and addition does not increase magnitude,
If the fifth bit of the 3r is set, the addition probagates and increases only if all bits are set after the fourth bit. Notice, fourth bit may be 0 or 1. I.e.,

Let

```
   n = b?*111
  3r = b1*?000
```

Step 1

```
  f(b?*111) = 3r + b10110
            = b1*?000 + b10110         || M + 1, from multiplication
            = b10*?110                 || M + 1, from addition
```

Step 2

```
  f(b10*?110) = b10*?11    || M - 1, from division
```  

By further investigation,

d.b.i) In b10*?11, if ? = 0, then a = b011 and the fourth bit is not set, the magnitude won't change due the addition of a to 3r.

Step 3 of d.b.i)

```
     n = b10*011         | from Step 2 and ? = 0

  f(n) = 3n + 1
       = 3 * b10*011 + 1
       = 3 * b10*000 + b10000
       = b110*10000            || M + 1, from multiplication
```

Step 4 of d.b.i)

Collapse four times 

```
  C(b110*10000, 4) = b110*1 || M - 4
```  

Therefore, in d.b.i) the magnitude of n will decrease by 2.


d.b.ii) In b10\*?11, If ? = 1, then a = b111 and the fifth bit is not set, the magnitude won't change.

Step 3 of d.b.ii)

```
  n = b10*111     | from Step 2 and ? = 1
```

If there is no 0s in b10\*111, then n = b1111

Let's demonstrate how the algorithm processes b1111:

```
  n       r           a      +
  b1111
          b1000       b111
                * 3
        = b11000
                             + b10110
  = b101110
               >> 1
  = b10111
          b10000      b111
                * 3
       = b110000
	                     + b10110
  = b1000110
               >> 1
  = b100011
          b100000     b011   
                * 3          + b1010
  = b11001010
               >> 1
  = b1100101
          b1100000    b101   
                * 3          + b10000
  = b1001010000
               >> 4
  = b100101
          b100000     b101  
                * 3          + b10000
  = b1110000
               >> 4
  = b111
          b0          b111  
                * 3          + b10110
  = b10110
               >> 1
  = b1011
          b1000       b011  
                * 3          + b1010
  = b100010
               >> 1
  = b10001
         b10000       b001   
                * 3          + b100
  = b110100
               >> 2
  = b1101
         b1000        b101   
                * 3          + b10000
  = b101000
               >> 3
  = b101
         b0           b101
                * 3          + b10000
  = b10000
               >> 4
  = b1
```

Let's show the same with one 0 in b10\*111, then n = b10111. The process is presented in more compacted form:

```
n           r           a      +             M
b10111      10000 *3    111    + 10110     5+2
b1000110 >> 1                               -1
b100011     100000 *3   011    + b1010      +1
b1101010 >> 1                               -1
b110101     110000 *3   101    + b10000     +2
b10100000 >> 5                              -5
b101        b0 *       b101    + b10000     +2
b10000 >> 4                                 -4
b1                                           1
```

And for arbitrary number of 0s (more than one) in b10\*111.

```
n                 r                a       +            M
b10*111           b10*000      *3  b111    + b10110    +1
b110*10110 >> 1                                        -1
b110*1011         b110*1000    *3  b011    + b1010     +2
b10010*100010 >> 1                                     -1
b10010*10001      b10010*10000 *3  b001    + b100      +1
b110110*110100 >> 2                                    -2
b110110*1101      b110110*1000 *3  b101    + b10000    +2
b10100010*101000 >> 3                                  -3
b10100010*101     b0          * 3  b101    + b10000    +1
b111100110*10000 >> 3                                  -3
b111100110*1 [!]  b111100110*  *3  b001    + b100      +2
b10110110010*100 >> 2                                  -2
b10110110010*1                                         -3 [!] 
```

We start repeating a = b001 and eat all the 0s from the middle. The magnitude is reduced by three in total.

First step of the previous processing explained:

```
f(n) = 3n + 1 
     = 3 * b10*111 + 1         || r=b10*000, a=b111
     = 3 * b10*000 + b10110    || +=b10110
     = b110*10110              || M + 1, from multiplication
```

Summary of a)-d) 

```
a)      |f(f(f(n)))| = |n| - 1, if n=b?*001

b.i)    |f(b?*011)| = |b?*011| + 2          if addition of one increases M by 1
        |f(f(b?*011))| = |b?*011| + 1       if addition of one increases M by 1
        f(f(b?*011)) = b10*01               next step is to repeat a) as long as lowest bits are b001, each repeation reduces M by 1.
                                            repeat until the pattern is b101 which is shown to be 1 after some more iterations.
					    
b.ii)   |f(b?*011)| = |b?*011| + 1          if addition does not increase M by 1
        |f(f(b?*011))| = |b?*011|           if adding does not propagate.
        f(f(b?*011)) = b?*101               next step is to apply c) to this pattern

c)      |f(f(f(f(b?*101))))| = |?*101| - 2  if ?* contains at least one zero before HSB. 
        C(f(b?*101)) = 1                    if ?* == 1*

d.a)    |f(f(?*111))| = |?*111|             if the fifth bit of the 3r is not set.
         f(f(b?*111)) = b?*1?11

d.a.i)  If ? in result is 0, the pattern is b?*1011 and the next step is b).

d.a.ii) If ? in result is 1, the pattern is b?*1111.
        |f(f(f(f(b?*1111))))| = |b?*1111|
          f(f(f(f(b?*1111)))) = b?*0011          next step is b).

d.b)  |f(f(b?*111))| = |b?*111| + 1
        f(f(b?*111)) = b10*?11

d.b.i) |C(f(f(f(b?*111))), 4)| = |b?*111| - 2

d.b.ii) the algorithm stops at 1 or the magnitude is reduced by three in total.
```

Conclusion
----------

The designed algorithm calculates f(n), stops when f(n) results to 1, and stops for every natural number n > 0. 
Therefore the Collatz conjecture is shown to be true for every $n \in N (> 0)$.
