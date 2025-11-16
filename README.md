Proof of Collatz conjecture with a computer scientific look
===========================================================
The repository contains a proposal to prove Collatz conjecture using bit patterns and by showing the change of magnitude of bit presentation of the number will eventually decrease towards one when calculation of f(n) is iterated repeadetly. 

16th of November 2025
by Sami Mäkinen <sami.o.makinen@gmail.com> 

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

This paper proposes an other trial of proof of the Collatz conjecture. While the author sincerely believes the proof is valid, it requires validation and acceptance from scientific community. So, takes this with a grain of salt.

The proposal of proof is published openly for criticism and inspection.

About the proof
---------------

The proof starts with presentation of the new algorithm which iterates the steps using binary operations and eventually reaches 1 for any given number.

The proof relies on the observation that magnitude of number's binary presentation (number of bits in presentation) may increase and decrease on iterations and after careful study, the magnitude will eventually decrease. Finally, the magnitude will reach 1 when f(n) = 1.

The proof consist of three theorems and each theorem is demonstrated to be true. 
- the algorithm calculates the f(n),
- the algorithm stops when result is 1 for any n,
- the algorithm is decidable and stops for any n. 

As a conclusion, the theorems form a proof of Collatz conjecture.

About the notation
------------------

A number presented in binary format is only 0s and 1s. Each bit n presents value $2^i$, i >= 0. If the bit is 0, the value of the bit is 0, otherwise $2^i$ where i is the position of the bit. The value is sum of the bit presentations. The rightmost bit at position 0 of the binary presentation is called lowest significant bit (LSB). The leftmost bit of the binary presentation is called highest significant (HSB) bit.

In the paper the numbers are natural numbers $n \in N (> 0)$ and the binary presentation do not have a sign bit nor decimal fraction bits.

To avoid confusion between different bases the binary number is prefixed with a b. For example b11 is three while 11 is eleven.

If binary number is odd, the LSB is one. If the LSB is 0, the number is even. The LSB presents 1 if the bit is set. The other bits present even values $2^i (i > 0)$.

The special symbol \* is used to present 0 or more bits in sequence. Thus, 1\* is sequence of zero or more ones.

The 01\* presents a sequence of bits where the 0 is followed by zero or more number of 1-bits. Similarly, 10\* presents a sequence of bits where the 1 is followed any number of 0-bits. The special symbol ? is used when the bit value is unknown. The ? can be either 0 or 1. The ?\* is sequence of any bits and has length of 0 or more.

If 0 is added to ? the result is ?.  

If 1 is added to ? the result is 10\*, because if ? is 0, the result is 1 and, if ? is 1, the result is 10.  

If ? is added to ? the result is ?\*, because the choices are: 0+0 = 0, 0+1 = 1, 1+0=1, 1+1=10.  

If 0 is added to 01\* the result is 01\*.  

If 1 is added to 01\* the result is 10\*.  

If 0 is added to 10\* the result is 10\*.  

If 1 is added to 10\* the result is 10\*1.  

if ? is added to 1\*, the result is 1\*?.

If 0, 1 or ? is added to ?\*, the result is ?\*. The adding of 0 won't change the binary sequence. The adding of 1 will change the binary sequence but because we don't know how, the result is ?\*.

The notation n >> x means that the bits of n are shifted to the right x times. This is equal to division of n by $2^x$.

n >> x = n / $2^x$

Some remarks about division by two (shifting to the right by 1). Notice: this would lead to rounding down, if pattern presents odd number.

b1 >> 1 = b0

b1\* >> 1 = b1\*

b1\*0 >> 1 = b1\*

b? >> 1 = b0

b?\* >> 1 = b?\*

b?0 >> 1 = b?

b?\*0 >> 1 = b?\*

The notation n << x means that the bits of n are shifted to the left x times. This is equal to multiplication of n by $2^x$.

n << x = n \* $2^x$

Some remarks about multiplication by two (shifting to the left by 1).

b1 << 1 = b10

b1\* << 1 = b1\*0.

b? << 1 = ?0.

b?\* << 1 = ?\*0.

The minimum length of the bit string needed to present a number in binary presentation is called magnitude of the binary number and marked with M. The right-most 0s are ignored when calculating the
magnitude. Thus, b000100 magnitude is 3 because the right-most three zeros are ignored.

The magnitude M of bit string n is |n|. Simply, M = |n| Some rules about magnitude of n:

|0| = 0

|1| = 1

|?| = 0 or 1

|0\*| = 0

|10\*| >= 1

|1\*| >= 0

|1?\*| >= 1

|1?\* << 1| = |1?\*| + 1

|1?\* >> 1| = |1?\*| - 1

Insights of calculating f(n) with binary operations
---------------------------------------------------

The multiplication of binary number by two is equal to shifting the bits to the left towards highest significant bit. Equally the division of binary number is shifting the bits to the right towards least
significant bit. If the binary number is odd, then the division by two will be rounded down to closest natural number. In the Collatz sequence the division by two will occur only to even numbers, so there
will be no rounding down.

**Corollary:** The 3n will result to odd number, if the n is odd. This can be easily proved using binary numbers.

  3n <=> 2n + n

Let a be the binary pattern of n. Because n is odd the LSB is 1.

  a = b?\*1

2n will result to ba0 = b?\*10, because of the shift left. By adding n will result to ?\*1, because LSB is set in n.

```math
\begin{equation}
\frac{
    \begin{array}[b]{r}
      \left( ?^*1 0 \right) \\
      +  \left( ?^* 1 \right) 
    \end{array}
  }{
    \left( ?^* 1 \right)
  }
\end{equation}
```

The algorithm
-------------

The algorithm treats even numbers by dividing the number by two as in f(n). If the result of division is still even, we continue dividing as long the result is not even. We say the result is collapsed to even and use notation C(n) where pattern of n is 1?\*10\*. After C(n) = C(1?\*10\*) = 1?\*1

If the number is odd, the algorithm uses different step depending on the three lowest significant bits.  The three lowest bits are examined because we want to know whether the result is even or odd and, if the
result can be collapsed. If the LSB is 1, the result is odd. If the LSB is 0, the result is even and can be divided by two.

When n is odd the format is 1?\*1. If considering the three least significant bits we have following choices:

  a) b001
  b) b011
  c) b101
  d) b111

Let's check what happens to these when f(n) is applied to them.

a) The algorithm will halt for the result being one. Let's check still what happens to b001, if f(n) is applied to it:

f(b001) = 3 \* b001 + 1 = b011 + 1 = b100. 

The result is even and can be shifted twice to get odd number b1. In other words, to result is same.

If applied to a pattern of b1?\*001, the result would be

f(b1?\*001) = 3 \* b1?\*000 + b100 = b110?\*100

and next steps would collapse it to b110?\*1. Then algorithm would pick one of a)-d) depending on last three bits b??1.

b) f(b011) = 3 \* b011 + 1 = b1001 + 1 = b1010. 

The result is even and can be shifted once to get odd number b101. From c), we can see that b101 applying f(n) to it will result to b1.
Notice, if the pattern is b1?\*011, adding one will propagate toward HSB and must be resolved as well.

c) f(b101) = 3 \* b101 + 1 = b1111 + 1 = b10000. 

The result is even and can be shifted four times to get odd number = b1. Notice, if the pattern is b1?\*101, adding one will propagate toward HSB and must be resolved as well.

d) f(b111) = 3 \* b111 + 1 = b10101 + 1 = b10110. 

The result is even and can be shifted once to get odd number n = b1011. The n can be split

n = b1011 = b1000 + b011

=> f(n) = 3n + 1 = 3 \* (b1000 + b011) + 1 

= 3 \* b1000 + 3 \* b011 + 1 

= 3 \* b1000 + f(b011)    | From b), we notice that f(b011) is equal to b101. 

= 3 \* b1000 + b101 = b11101

f(b11101) = 3 \* b11000 + 3 \* b101 + 1 

= 3 \* b11000 + f(b101) 

= 3 \* b11000 + b10000 = b101000

Shifting b101000 will result to b101 and from c) we can conclude final result b1.

Notice, if the pattern is b1?\*111, adding one will propagate toward HSB and must be resolved as well.

Building the algorithm
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

Part 1 of the proof: Algorithm calculates f(n)
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
=> 3n + 1 = 3r + 3a + 1 
= 3r + 3 + 1
= 3r + 4           || 4 is b100
```
`
In lines 18-22: If a is 3 (b011)

```
=> 3n + 1 = 3r + 3a + 1
= 3r + 9 + 1
= 3r + 10          || 10 is b1010
```

In lines 24-30: If a is 5 (b101)

```
=> 3n + 1 = 3r + 3a + 1
= 3r + 15 + 1
= 3r + 16          || 16 is b10000
```

In lines 32-36: If a is 7 (b111)

```
=> 3n + 1 = 3r + 3a + 1
= 3r + 21 + 1
= 3r + 22           || 22 is b10110
```

Part 2 of the proof: The algorithm will stop when result is 1 for every n
--------------------------------------------------------------------------

From lines 1, 5, 15, 21, 28, 35: The algorithm loops and sets n = f(n) in every loop, until n == 1, when the iteration stops.

Part 3 of the proof: The algorithm will stop for every n
--------------------------------------------------------

When algorithm calculates and sets n=f(n), the magnitude of n changes in every loop depending on n's the lower three bits in each iteration. The proof relies on the observation that magnitude of n may increase and decrease on iterations and after careful study, the magnitude will eventually decrease. Finally, the magnitude will reach 1 when n = 1.

a) with a = b001, 

**Lemma**: |f(f(f(n)))| = |n| - 1, if n=b?\*001 

Proof:

3\*n will increase the magnitude by one, but adding one does not. The addition will touch only the lowest three bits. Therefore, magnitude will remain the same or get smaller.

```
n = b?*001
M = |b?*001|
```

Step 1: 

```
f(n) = f(b?*001) = 3 * b?*001 + 1
= 3 * b?*000 + b100
= b?*000 + b100               || M + 1
= b?*100                      || M + 0
```

Step 2: 

`f(b?*100) = b?*10            || M - 1`

Step 3: 

```
f(b?*10) = b?*1               || M - 1
=> |f(f(f(b?*001)))| = |b?*001| - 1
```

b) with a = b011, there is two scenarios to be considered. Whether the addition of one in f(n) does increase the magnitude b.i) or does increases the magnitude b.ii).

b.i) The case when the addition of one increases the magnitude:

**Lemma**: If the fourth bit of the result of multiplication of r is set, the addition propagates and M increases only if all bits are set after the 3rd bit.  

Proof:

In other words, the addition of one increases M by 1, if 3r = b1\*000.

Let

```
n = b?*011
3r = b1*000
```

Step 1: 

```
f(n) = f(b?*011) = b?*011 * 3 + 1 = 3r + b1010
= b1*000 + b1010             || M + 1
= b10*010                    || M + 1
```

Step 2: 

`f(b10*010) = b10*01  || M - 1`

Step 3: 

`see a)               || M - 1`

After division the result is b10\*001, and again this pattern leads to magnitude decrease due the a = b001.  The step 3 will result to same pattern b10\*001 but with one 0 less. This will repeat until the pattern is b101 which is shown to be 1 after some more iterations.

So, in case of a = b011 the magnitude of n will start decreasing after third iteration.

b.ii) Case the addition of one does not increase the magnitude:

**Lemma**: |f(f(3n+1))| = |n| + 1 - 1 = |n|, if adding does not propagate.

Proof:

The result is `f(b?*011) = 3*r + b1010`. If fourth bit of the 3\*r is not set, the magnitude won't change due adding 1.

Let 

```
n = b?*011
3r = b?*0000   || 4th bit not set after multiplication`
```

Step 1: 

```
f(n) = f(b?*011) = b?*011 * 3 + 1 = 3r + b1010
= b?*0000 + b1010            || M + 1
= b?*1010                    || M + 0
```

Step 2:  

```
f(b?*1010) = b?*101         || M - 1
=> |f(f(b?*011))| = |b?*011|, if 3r = b?*0000 in the first step.
```
The result is b?\*101 and magnitude stays same. From c) we can see that next step reduces the magnitude.

The zero bit does not need to be 4th bit. The result is same if the zero bit is anywhere in the 3\*r result.

**Lemma**: If 3\*r is not b1\*000, the magnitude won't change due adding one. The propagation of addition stops at first zero bit. 

Proof:

In that case 3\*r is b?\*01\*000.

Let

```
n=b?*101
3*r = b?*01*000

f(b?*101) = 3*r + b1010
= b?*01*000` + b1010      || M + 1
= b?*10*010
```

Step 2:

`f(b?*10*010) = b?*10*01   || M - 1`


c) with a = b101, 

**Lemma**: |f(f(3n+1))| = |n| - 2, if n=?*101

The adding will increase magnitude, if r = b1\*000. This would lead to following pattern:

`b1*000 + b10000 = 10*`

After collapse the result is b1 and magnitude is 1.

d) with a = b111, 

`|f(f(3n+1))| = |n| + 1 - 1 = |n|`

In case of a = b111, the result is n = 3\*r + b10110.

d).a If the fifth bit of the 3\*r is not set, the magnitude won't change.

d).b If the bit is set, the addition probagates and increases only if all bits are set after the fourth bit. Notice, fourth bit may be 0 or 1. I.e.,

`3*r + b10110 = b1*?000 + b10110 = b10*?110 || M + 2`

After division 

`b10*?11.     || M - 1`

d).c By further investigation,

d).c.i if ? = 0, then a = b011 and the fourth bit is not set, the magnitude won't change due the addition of a to 3r. Thus, the magnitude will remain the same. After this step pattern is:

```
n = b10*011
3n + 1 = 3 * b10*011 + 1
=> 3 * b10*000 + b10000
=> b110*10000    || M + 1
```

Collapse four times 

`=> b110*1 || M - 4`

d).c.ii If ? = 1, then a = b111 and the fifth bit is not set, the magnitude won't change.

`n = b10*111`

If there is no 0s, n = b1111

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
               *3         + b1010
= b11001010 >> 1
= b1100101
        b1100000    b101   
	       *3         + b10000
= b1001010000 >> 4
= b100101
        b100000     b101  
                * 3       + b10000
= b1110000 >> 4
= b111
        b0        b111  
           *3          + b10110
= b10110 >> 1
= b1011
       b1000      b011  
             * 3       + b1010
= b100010 >> 1
= b10001
       b10000       b001   
              * 3      + b100
= b110100 >> 2
= b1101
      b1000        b101   
             *3        + b10000
= b101000 >> 3
= b101
      b0           b101
         * 3           + b10000
= b10000 >> 4
= b1
```

Let's show the same with one 0, n = b10111. The process is presented in more compacted form:

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

And for arbitrary number of 0s.

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
Depending on how many 0s there are the r = $3^s$ and a = {001,011, 101, 111}  $3^s$ + {1,3,5,7}

First step explained:

```
3n + 1 
=> 3 * b10*111 + 1
= 3 * b10*000 + b10110
=> b110*10110 || M + 1
Collapse once => b110*1011 || M - 1
```

Conclusion
----------

The designed algorithm calculates f(n), stops when f(n) results to 1, and stops for every natural number n > 0. 
Therefore the Collatz conjecture is shown to be true for every n.

