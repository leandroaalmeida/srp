(function(factory) {
    if (typeof exports === 'object') {
        // CommonJS
        factory(require, exports, module);
    } else if (typeof define === 'function') {
        // AMD requirejs
        define(factory);
    } else {
        // Plain script tag
        var _module = {};
        _module.exports = {};
        var _require = function(name) { throw new Error("can't require"); }
        factory(_require, _module.exports, _module);
        window.BigInt = _module.exports;
    }
})(function (require, exports, module) {
    "use strict";

    var trueRandom = function () { return Math.random(); };

    function setRandom(random) {
        trueRandom = random;
    }

    //globals
    var bpe=0;         //bits stored per array element
    var mask=0;        //AND this with an array element to chop it down to bpe bits
    var radix=mask+1;  //equals 2^bpe.  A single 1 bit to the left of the last bit of mask.

    //the digits for converting to different bases
    var digitsStr='0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz_=!@#$%^&*()[]{}|;:,.<>/?`~ \\\'\"+-';

    //initialize the global variables
    for (bpe=0; (1<<(bpe+1)) > (1<<bpe); bpe++);  //bpe=number of bits in the mantissa on this platform
    bpe>>=1;                   //bpe=number of bits in one element of the array representing the bigInt
    mask=(1<<bpe)-1;           //AND the mask with an integer to get its bpe least significant bits
    radix=mask+1;              //2^bpe.  a single 1 bit to the left of the first bit of mask
    var one=int2bigInt(1,1,1);     //constant used in powMod_()

    //the following global variables are scratchpad memory to
    //reduce dynamic memory allocation in the inner loop
    var t=new Array(0);
    var ss=t;       //used in mult_()
    var s0=t;       //used in multMod_(), squareMod_()
    var s1=t;       //used in powMod_(), multMod_(), squareMod_()
    var s2=t;       //used in powMod_(), multMod_()
    var s3=t;       //used in powMod_()
    var s4= t, s5=t; //used in mod_()
    var s6=t;       //used in bigInt2str()
    var s7=t;       //used in powMod_()
    var T=t;        //used in GCD_()
    var sa=t;       //used in mont_()
    var mr_x1= t, mr_r= t, mr_a=t;                                      //used in millerRabin()
    var eg_v= t, eg_u= t, eg_A=t, eg_B=t, eg_C=t, eg_D=t;               //used in eGCD_(), inverseMod_()
    var md_q1=t, md_q2=t, md_q3=t, md_r=t, md_r1=t, md_r2=t, md_tt=t; //used in mod_()

    var primes=t, pows=t, s_i=t, s_i2=t, s_R=t, s_rm=t, s_q=t, s_n1=t;
    var s_a=t, s_r2=t, s_n=t, s_b=t, s_d=t, s_x1=t, s_x2=t, s_aa=t; //used in randTruePrime_()

    var rpprb=t; //used in randProbPrimeRounds() (which also uses "primes")

    ////////////////////////////////////////////////////////////////////////////////////////


    //return array of all primes less than integer n
    function findPrimes(n) {
      var i,s,p,ans;
      s=new Array(n);
      for (i=0;i<n;i++)
        s[i]=0;
      s[0]=2;
      p=0;    //first p elements of s are primes, the rest are a sieve
      for(;s[p]<n;) {                  //s[p] is the pth prime
        for(i=s[p]*s[p]; i<n; i+=s[p]) //mark multiples of s[p]
          s[i]=1;
        p++;
        s[p]=s[p-1]+1;
        for(; s[p]<n && s[s[p]]; s[p]++); //find next prime (where s[p]==0)
      }
      ans=new Array(p);
      for(i=0;i<p;i++)
        ans[i]=s[i];
      return ans;
    }


    //does a single round of Miller-Rabin base b consider x to be a possible prime?
    //x is a bigInt, and b is an integer, with b<x
    function millerRabinInt(x,b) {
      if (mr_x1.length!=x.length) {
        mr_x1=dup(x);
        mr_r=dup(x);
        mr_a=dup(x);
      }

      copyInt_(mr_a,b);
      return millerRabin(x,mr_a);
    }

    //does a single round of Miller-Rabin base b consider x to be a possible prime?
    //x and b are bigInts with b<x
    function millerRabin(x,b) {
      var i,j,k,s;

      if (mr_x1.length!=x.length) {
        mr_x1=dup(x);
        mr_r=dup(x);
        mr_a=dup(x);
      }

      copy_(mr_a,b);
      copy_(mr_r,x);
      copy_(mr_x1,x);

      addInt_(mr_r,-1);
      addInt_(mr_x1,-1);

      //s=the highest power of two that divides mr_r
      k=0;
      for (i=0;i<mr_r.length;i++)
        for (j=1;j<mask;j<<=1)
          if (x[i] & j) {
            s=(k<mr_r.length+bpe ? k : 0);
             i=mr_r.length;
             j=mask;
          } else
            k++;

      if (s)
        rightShift_(mr_r,s);

      powMod_(mr_a,mr_r,x);

      if (!equalsInt(mr_a,1) && !equals(mr_a,mr_x1)) {
        j=1;
        while (j<=s-1 && !equals(mr_a,mr_x1)) {
          squareMod_(mr_a,x);
          if (equalsInt(mr_a,1)) {
            return 0;
          }
          j++;
        }
        if (!equals(mr_a,mr_x1)) {
          return 0;
        }
      }
      return 1;
    }

    //returns how many bits long the bigInt is, not counting leading zeros.
    function bitSize(x) {
      var j,z,w;
      for (j=x.length-1; (x[j]==0) && (j>0); j--);
      for (z=0,w=x[j]; w; (w>>=1),z++);
      z+=bpe*j;
      return z;
    }

    //return a copy of x with at least n elements, adding leading zeros if needed
    function expand(x,n) {
      var ans=int2bigInt(0,(x.length>n ? x.length : n)*bpe,0);
      copy_(ans,x);
      return ans;
    }

    //return a k-bit true random prime using Maurer's algorithm.
    function randTruePrime(k) {
      var ans=int2bigInt(0,k,0);
      randTruePrime_(ans,k);
      return trim(ans,1);
    }

    //return a k-bit random probable prime with probability of error < 2^-80
    function randProbPrime(k) {
      if (k>=600) return randProbPrimeRounds(k,2); //numbers from HAC table 4.3
      if (k>=550) return randProbPrimeRounds(k,4);
      if (k>=500) return randProbPrimeRounds(k,5);
      if (k>=400) return randProbPrimeRounds(k,6);
      if (k>=350) return randProbPrimeRounds(k,7);
      if (k>=300) return randProbPrimeRounds(k,9);
      if (k>=250) return randProbPrimeRounds(k,12); //numbers from HAC table 4.4
      if (k>=200) return randProbPrimeRounds(k,15);
      if (k>=150) return randProbPrimeRounds(k,18);
      if (k>=100) return randProbPrimeRounds(k,27);
                  return randProbPrimeRounds(k,40); //number from HAC remark 4.26 (only an estimate)
    }

    //return a k-bit probable random prime using n rounds of Miller Rabin (after trial division with small primes)
    function randProbPrimeRounds(k,n) {
      var ans, i, divisible, B;
      B=30000;  //B is largest prime to use in trial division
      ans=int2bigInt(0,k,0);

      //optimization: try larger and smaller B to find the best limit.

      if (primes.length==0)
        primes=findPrimes(30000);  //check for divisibility by primes <=30000

      if (rpprb.length!=ans.length)
        rpprb=dup(ans);

      for (;;) { //keep trying random values for ans until one appears to be prime
        //optimization: pick a random number times L=2*3*5*...*p, plus a
        //   random element of the list of all numbers in [0,L) not divisible by any prime up to p.
        //   This can reduce the amount of random number generation.

        randBigInt_(ans,k,0); //ans = a random odd number to check
        ans[0] |= 1;
        divisible=0;

        //check ans for divisibility by small primes up to B
        for (i=0; (i<primes.length) && (primes[i]<=B); i++)
          if (modInt(ans,primes[i])==0 && !equalsInt(ans,primes[i])) {
            divisible=1;
            break;
          }

        //optimization: change millerRabin so the base can be bigger than the number being checked, then eliminate the while here.

        //do n rounds of Miller Rabin, with random bases less than ans
        for (i=0; i<n && !divisible; i++) {
          randBigInt_(rpprb,k,0);
          while(!greater(ans,rpprb)) //pick a random rpprb that's < ans
            randBigInt_(rpprb,k,0);
          if (!millerRabin(ans,rpprb))
            divisible=1;
        }

        if(!divisible)
          return ans;
      }
    }

    //return a new bigInt equal to (x mod n) for bigInts x and n.
    function mod(x,n) {
      var ans=dup(x);
      mod_(ans,n);
      return trim(ans,1);
    }

    //return (x+n) where x is a bigInt and n is an integer.
    function addInt(x,n) {
      var ans=expand(x,x.length+1);
      addInt_(ans,n);
      return trim(ans,1);
    }

    //return x*y for bigInts x and y. This is faster when y<x.
    function mult(x,y) {
      var ans=expand(x,x.length+y.length);
      mult_(ans,y);
      return trim(ans,1);
    }

    //return (x**y mod n) where x,y,n are bigInts and ** is exponentiation.  0**0=1. Faster for odd n.
    function powMod(x,y,n) {
      var ans=expand(x,n.length);
      powMod_(ans,trim(y,2),trim(n,2),0);  //this should work without the trim, but doesn't
      return trim(ans,1);
    }

    //return (x-y) for bigInts x and y.  Negative answers will be 2s complement
    function sub(x,y) {
      var ans=expand(x,(x.length>y.length ? x.length+1 : y.length+1));
      sub_(ans,y);
      return trim(ans,1);
    }

    //return (x+y) for bigInts x and y.
    function add(x,y) {
      var ans=expand(x,(x.length>y.length ? x.length+1 : y.length+1));
      add_(ans,y);
      return trim(ans,1);
    }

    //return (x**(-1) mod n) for bigInts x and n.  If no inverse exists, it returns null
    function inverseMod(x,n) {
      var ans=expand(x,n.length);
      var s;
      s=inverseMod_(ans,n);
      return s ? trim(ans,1) : null;
    }

    //return (x*y mod n) for bigInts x,y,n.  For greater speed, let y<x.
    function multMod(x,y,n) {
      var ans=expand(x,n.length);
      multMod_(ans,y,n);
      return trim(ans,1);
    }

    //generate a k-bit true random prime using Maurer's algorithm,
    //and put it into ans.  The bigInt ans must be large enough to hold it.
    function randTruePrime_(ans,k) {
      var c,m,pm,dd,j,r,B,divisible,w,z,zz,recSize;

      if (primes.length==0)
        primes=findPrimes(30000);  //check for divisibility by primes <=30000

      if (pows.length==0) {
        pows=new Array(512);
        for (j=0;j<512;j++) {
          pows[j]=Math.pow(2,j/511.-1.);
        }
      }

      //c and m should be tuned for a particular machine and value of k, to maximize speed
      c=0.1;  //c=0.1 in HAC
      m=20;   //generate this k-bit number by first recursively generating a number that has between k/2 and k-m bits
      var recLimit=20; //stop recursion when k <=recLimit.  Must have recLimit >= 2

      if (s_i2.length!=ans.length) {
        s_i2=dup(ans);
        s_R =dup(ans);
        s_n1=dup(ans);
        s_r2=dup(ans);
        s_d =dup(ans);
        s_x1=dup(ans);
        s_x2=dup(ans);
        s_b =dup(ans);
        s_n =dup(ans);
        s_i =dup(ans);
        s_rm=dup(ans);
        s_q =dup(ans);
        s_a =dup(ans);
        s_aa=dup(ans);
      }

      if (k <= recLimit) {  //generate small random primes by trial division up to its square root
        pm=(1<<((k+2)>>1))-1; //pm is binary number with all ones, just over sqrt(2^k)
        copyInt_(ans,0);
        for (dd=1;dd;) {
          dd=0;
          ans[0]= 1 | (1<<(k-1)) | Math.floor(trueRandom()*(1<<k));  //random, k-bit, odd integer, with msb 1
          for (j=1;(j<primes.length) && ((primes[j]&pm)==primes[j]);j++) { //trial division by all primes 3...sqrt(2^k)
            if (0==(ans[0]%primes[j])) {
              dd=1;
              break;
            }
          }
        }
        carry_(ans);
        return;
      }

      B=c*k*k;    //try small primes up to B (or all the primes[] array if the largest is less than B).
      if (k>2*m)  //generate this k-bit number by first recursively generating a number that has between k/2 and k-m bits
        for (r=1; k-k*r<=m; )
          r=pows[Math.floor(trueRandom()*512)];   //r=Math.pow(2,Math.random()-1);
      else
        r=.5;

      //simulation suggests the more complex algorithm using r=.333 is only slightly faster.

      recSize=Math.floor(r*k)+1;

      randTruePrime_(s_q,recSize);
      copyInt_(s_i2,0);
      s_i2[Math.floor((k-2)/bpe)] |= (1<<((k-2)%bpe));   //s_i2=2^(k-2)
      divide_(s_i2,s_q,s_i,s_rm);                        //s_i=floor((2^(k-1))/(2q))

      z=bitSize(s_i);

      for (;;) {
        for (;;) {  //generate z-bit numbers until one falls in the range [0,s_i-1]
          randBigInt_(s_R,z,0);
          if (greater(s_i,s_R))
            break;
        }                //now s_R is in the range [0,s_i-1]
        addInt_(s_R,1);  //now s_R is in the range [1,s_i]
        add_(s_R,s_i);   //now s_R is in the range [s_i+1,2*s_i]

        copy_(s_n,s_q);
        mult_(s_n,s_R);
        multInt_(s_n,2);
        addInt_(s_n,1);    //s_n=2*s_R*s_q+1

        copy_(s_r2,s_R);
        multInt_(s_r2,2);  //s_r2=2*s_R

        //check s_n for divisibility by small primes up to B
        for (divisible=0,j=0; (j<primes.length) && (primes[j]<B); j++)
          if (modInt(s_n,primes[j])==0 && !equalsInt(s_n,primes[j])) {
            divisible=1;
            break;
          }

        if (!divisible)    //if it passes small primes check, then try a single Miller-Rabin base 2
          if (!millerRabinInt(s_n,2)) //this line represents 75% of the total runtime for randTruePrime_
            divisible=1;

        if (!divisible) {  //if it passes that test, continue checking s_n
          addInt_(s_n,-3);
          for (j=s_n.length-1;(s_n[j]==0) && (j>0); j--);  //strip leading zeros
          for (zz=0,w=s_n[j]; w; (w>>=1),zz++);
          zz+=bpe*j;                             //zz=number of bits in s_n, ignoring leading zeros
          for (;;) {  //generate z-bit numbers until one falls in the range [0,s_n-1]
            randBigInt_(s_a,zz,0);
            if (greater(s_n,s_a))
              break;
          }                //now s_a is in the range [0,s_n-1]
          addInt_(s_n,3);  //now s_a is in the range [0,s_n-4]
          addInt_(s_a,2);  //now s_a is in the range [2,s_n-2]
          copy_(s_b,s_a);
          copy_(s_n1,s_n);
          addInt_(s_n1,-1);
          powMod_(s_b,s_n1,s_n);   //s_b=s_a^(s_n-1) modulo s_n
          addInt_(s_b,-1);
          if (isZero(s_b)) {
            copy_(s_b,s_a);
            powMod_(s_b,s_r2,s_n);
            addInt_(s_b,-1);
            copy_(s_aa,s_n);
            copy_(s_d,s_b);
            GCD_(s_d,s_n);  //if s_b and s_n are relatively prime, then s_n is a prime
            if (equalsInt(s_d,1)) {
              copy_(ans,s_aa);
              return;     //if we've made it this far, then s_n is absolutely guaranteed to be prime
            }
          }
        }
      }
    }

    //Return an n-bit random BigInt (n>=1).  If s=1, then the most significant of those n bits is set to 1.
    function randBigInt(n,s) {
      var a,b;
      a=Math.floor((n-1)/bpe)+2; //# array elements to hold the BigInt with a leading 0 element
      b=int2bigInt(0,0,a);
      randBigInt_(b,n,s);
      return b;
    }

    //Set b to an n-bit random BigInt.  If s=1, then the most significant of those n bits is set to 1.
    //Array b must be big enough to hold the result. Must have n>=1
    function randBigInt_(b,n,s) {
      var i,a;
      for (i=0;i<b.length;i++)
        b[i]=0;
      a=Math.floor((n-1)/bpe)+1; //# array elements to hold the BigInt
      for (i=0;i<a;i++) {
        b[i]=Math.floor(trueRandom()*(1<<(bpe-1)));
      }
      b[a-1] &= (2<<((n-1)%bpe))-1;
      if (s==1)
        b[a-1] |= (1<<((n-1)%bpe));
    }

    //Return the greatest common divisor of bigInts x and y (each with same number of elements).
    function GCD(x,y) {
      var xc,yc;
      xc=dup(x);
      yc=dup(y);
      GCD_(xc,yc);
      return xc;
    }

    //set x to the greatest common divisor of bigInts x and y (each with same number of elements).
    //y is destroyed.
    function GCD_(x,y) {
      var i,xp,yp,A,B,C,D,q,sing;
      if (T.length!=x.length)
        T=dup(x);

      sing=1;
      while (sing) { //while y has nonzero elements other than y[0]
        sing=0;
        for (i=1;i<y.length;i++) //check if y has nonzero elements other than 0
          if (y[i]) {
            sing=1;
            break;
          }
        if (!sing) break; //quit when y all zero elements except possibly y[0]

        for (i=x.length;!x[i] && i>=0;i--);  //find most significant element of x
        xp=x[i];
        yp=y[i];
        A=1; B=0; C=0; D=1;
        while ((yp+C) && (yp+D)) {
          q =Math.floor((xp+A)/(yp+C));
          var qp=Math.floor((xp+B)/(yp+D));
          if (q!=qp)
            break;
          t= A-q*C;   A=C;   C=t;    //  do (A,B,xp, C,D,yp) = (C,D,yp, A,B,xp) - q*(0,0,0, C,D,yp)
          t= B-q*D;   B=D;   D=t;
          t=xp-q*yp; xp=yp; yp=t;
        }
        if (B) {
          copy_(T,x);
          linComb_(x,y,A,B); //x=A*x+B*y
          linComb_(y,T,D,C); //y=D*y+C*T
        } else {
          mod_(x,y);
          copy_(T,x);
          copy_(x,y);
          copy_(y,T);
        }
      }
      if (y[0]==0)
        return;
      t=modInt(x,y[0]);
      copyInt_(x,y[0]);
      y[0]=t;
      while (y[0]) {
        x[0]%=y[0];
        t=x[0]; x[0]=y[0]; y[0]=t;
      }
    }

    //do x=x**(-1) mod n, for bigInts x and n.
    //If no inverse exists, it sets x to zero and returns 0, else it returns 1.
    //The x array must be at least as large as the n array.
    function inverseMod_(x,n) {
      var k=1+2*Math.max(x.length,n.length);

      if(!(x[0]&1)  && !(n[0]&1)) {  //if both inputs are even, then inverse doesn't exist
        copyInt_(x,0);
        return 0;
      }

      if (eg_u.length!=k) {
        eg_u=new Array(k);
        eg_v=new Array(k);
        eg_A=new Array(k);
        eg_B=new Array(k);
        eg_C=new Array(k);
        eg_D=new Array(k);
      }

      copy_(eg_u,x);
      copy_(eg_v,n);
      copyInt_(eg_A,1);
      copyInt_(eg_B,0);
      copyInt_(eg_C,0);
      copyInt_(eg_D,1);
      for (;;) {
        while(!(eg_u[0]&1)) {  //while eg_u is even
          halve_(eg_u);
          if (!(eg_A[0]&1) && !(eg_B[0]&1)) { //if eg_A==eg_B==0 mod 2
            halve_(eg_A);
            halve_(eg_B);
          } else {
            add_(eg_A,n);  halve_(eg_A);
            sub_(eg_B,x);  halve_(eg_B);
          }
        }

        while (!(eg_v[0]&1)) {  //while eg_v is even
          halve_(eg_v);
          if (!(eg_C[0]&1) && !(eg_D[0]&1)) { //if eg_C==eg_D==0 mod 2
            halve_(eg_C);
            halve_(eg_D);
          } else {
            add_(eg_C,n);  halve_(eg_C);
            sub_(eg_D,x);  halve_(eg_D);
          }
        }

        if (!greater(eg_v,eg_u)) { //eg_v <= eg_u
          sub_(eg_u,eg_v);
          sub_(eg_A,eg_C);
          sub_(eg_B,eg_D);
        } else {                   //eg_v > eg_u
          sub_(eg_v,eg_u);
          sub_(eg_C,eg_A);
          sub_(eg_D,eg_B);
        }

        if (equalsInt(eg_u,0)) {
          while (negative(eg_C)) //make sure answer is nonnegative
            add_(eg_C,n);
          copy_(x,eg_C);

          if (!equalsInt(eg_v,1)) { //if GCD_(x,n)!=1, then there is no inverse
            copyInt_(x,0);
            return 0;
          }
          return 1;
        }
      }
    }

    //return x**(-1) mod n, for integers x and n.  Return 0 if there is no inverse
    function inverseModInt(x,n) {
      var a=1,b=0,t;
      for (;;) {
        if (x==1) return a;
        if (x==0) return 0;
        b-=a*Math.floor(n/x);
        n%=x;

        if (n==1) return b; //to avoid negatives, change this b to n-b, and each -= to +=
        if (n==0) return 0;
        a-=b*Math.floor(x/n);
        x%=n;
      }
    }

    //this deprecated function is for backward compatibility only.
    function inverseModInt_(x,n) {
       return inverseModInt(x,n);
    }


    //Given positive bigInts x and y, change the bigints v, a, and b to positive bigInts such that:
    //     v = GCD_(x,y) = a*x-b*y
    //The bigInts v, a, b, must have exactly as many elements as the larger of x and y.
    function eGCD_(x,y,v,a,b) {
      var g=0;
      var k=Math.max(x.length,y.length);
      if (eg_u.length!=k) {
        eg_u=new Array(k);
        eg_A=new Array(k);
        eg_B=new Array(k);
        eg_C=new Array(k);
        eg_D=new Array(k);
      }
      while(!(x[0]&1)  && !(y[0]&1)) {  //while x and y both even
        halve_(x);
        halve_(y);
        g++;
      }
      copy_(eg_u,x);
      copy_(v,y);
      copyInt_(eg_A,1);
      copyInt_(eg_B,0);
      copyInt_(eg_C,0);
      copyInt_(eg_D,1);
      for (;;) {
        while(!(eg_u[0]&1)) {  //while u is even
          halve_(eg_u);
          if (!(eg_A[0]&1) && !(eg_B[0]&1)) { //if A==B==0 mod 2
            halve_(eg_A);
            halve_(eg_B);
          } else {
            add_(eg_A,y);  halve_(eg_A);
            sub_(eg_B,x);  halve_(eg_B);
          }
        }

        while (!(v[0]&1)) {  //while v is even
          halve_(v);
          if (!(eg_C[0]&1) && !(eg_D[0]&1)) { //if C==D==0 mod 2
            halve_(eg_C);
            halve_(eg_D);
          } else {
            add_(eg_C,y);  halve_(eg_C);
            sub_(eg_D,x);  halve_(eg_D);
          }
        }

        if (!greater(v,eg_u)) { //v<=u
          sub_(eg_u,v);
          sub_(eg_A,eg_C);
          sub_(eg_B,eg_D);
        } else {                //v>u
          sub_(v,eg_u);
          sub_(eg_C,eg_A);
          sub_(eg_D,eg_B);
        }
        if (equalsInt(eg_u,0)) {
          while (negative(eg_C)) {   //make sure a (C) is nonnegative
            add_(eg_C,y);
            sub_(eg_D,x);
          }
          multInt_(eg_D,-1);  ///make sure b (D) is nonnegative
          copy_(a,eg_C);
          copy_(b,eg_D);
          leftShift_(v,g);
          return;
        }
      }
    }


    //is bigInt x negative?
    function negative(x) {
      return ((x[x.length-1]>>(bpe-1))&1);
    }


    //is (x << (shift*bpe)) > y?
    //x and y are nonnegative bigInts
    //shift is a nonnegative integer
    function greaterShift(x,y,shift) {
      var i, kx=x.length, ky=y.length;
      var k=((kx+shift)<ky) ? (kx+shift) : ky;
      for (i=ky-1-shift; i<kx && i>=0; i++)
        if (x[i]>0)
          return 1; //if there are nonzeros in x to the left of the first column of y, then x is bigger
      for (i=kx-1+shift; i<ky; i++)
        if (y[i]>0)
          return 0; //if there are nonzeros in y to the left of the first column of x, then x is not bigger
      for (i=k-1; i>=shift; i--)
        if      (x[i-shift]>y[i]) return 1;
        else if (x[i-shift]<y[i]) return 0;
      return 0;
    }

    //is x > y? (x and y both nonnegative)
    function greater(x,y) {
      var i;
      var k=(x.length<y.length) ? x.length : y.length;

      for (i=x.length;i<y.length;i++)
        if (y[i])
          return 0;  //y has more digits

      for (i=y.length;i<x.length;i++)
        if (x[i])
          return 1;  //x has more digits

      for (i=k-1;i>=0;i--)
        if (x[i]>y[i])
          return 1;
        else if (x[i]<y[i])
          return 0;
      return 0;
    }

    //divide x by y giving quotient q and remainder r.  (q=floor(x/y),  r=x mod y).  All 4 are bigints.
    //x must have at least one leading zero element.
    //y must be nonzero.
    //q and r must be arrays that are exactly the same length as x. (Or q can have more).
    //Must have x.length >= y.length >= 2.
    function divide_(x,y,q,r) {
      var kx, ky;
      var i,j,y1,y2,c,a,b;
      copy_(r,x);
      for (ky=y.length;y[ky-1]==0;ky--); //ky is number of elements in y, not including leading zeros

      //normalize: ensure the most significant element of y has its highest bit set
      b=y[ky-1];
      for (a=0; b; a++)
        b>>=1;
      a=bpe-a;  //a is how many bits to shift so that the high order bit of y is leftmost in its array element
      leftShift_(y,a);  //multiply both by 1<<a now, then divide both by that at the end
      leftShift_(r,a);

      //Rob Visser discovered a bug: the following line was originally just before the normalization.
      for (kx=r.length;r[kx-1]==0 && kx>ky;kx--); //kx is number of elements in normalized x, not including leading zeros

      copyInt_(q,0);                      // q=0
      while (!greaterShift(y,r,kx-ky)) {  // while (leftShift_(y,kx-ky) <= r) {
        subShift_(r,y,kx-ky);             //   r=r-leftShift_(y,kx-ky)
        q[kx-ky]++;                       //   q[kx-ky]++;
      }                                   // }

      for (i=kx-1; i>=ky; i--) {
        if (r[i]==y[ky-1])
          q[i-ky]=mask;
        else
          q[i-ky]=Math.floor((r[i]*radix+r[i-1])/y[ky-1]);

        //The following for(;;) loop is equivalent to the commented while loop,
        //except that the uncommented version avoids overflow.
        //The commented loop comes from HAC, which assumes r[-1]==y[-1]==0
        //  while (q[i-ky]*(y[ky-1]*radix+y[ky-2]) > r[i]*radix*radix+r[i-1]*radix+r[i-2])
        //    q[i-ky]--;
        for (;;) {
          y2=(ky>1 ? y[ky-2] : 0)*q[i-ky];
          c=y2>>bpe;
          y2=y2 & mask;
          y1=c+q[i-ky]*y[ky-1];
          c=y1>>bpe;
          y1=y1 & mask;

          if (c==r[i] ? y1==r[i-1] ? y2>(i>1 ? r[i-2] : 0) : y1>r[i-1] : c>r[i])
            q[i-ky]--;
          else
            break;
        }

        linCombShift_(r,y,-q[i-ky],i-ky);    //r=r-q[i-ky]*leftShift_(y,i-ky)
        if (negative(r)) {
          addShift_(r,y,i-ky);         //r=r+leftShift_(y,i-ky)
          q[i-ky]--;
        }
      }

      rightShift_(y,a);  //undo the normalization step
      rightShift_(r,a);  //undo the normalization step
    }

    //do carries and borrows so each element of the bigInt x fits in bpe bits.
    function carry_(x) {
      var i,k,c,b;
      k=x.length;
      c=0;
      for (i=0;i<k;i++) {
        c+=x[i];
        b=0;
        if (c<0) {
          b=-(c>>bpe);
          c+=b*radix;
        }
        x[i]=c & mask;
        c=(c>>bpe)-b;
      }
    }

    //return x mod n for bigInt x and integer n.
    function modInt(x,n) {
      var i,c=0;
      for (i=x.length-1; i>=0; i--)
        c=(c*radix+x[i])%n;
      return c;
    }

    //convert the integer t into a bigInt with at least the given number of bits.
    //the returned array stores the bigInt in bpe-bit chunks, little endian (buff[0] is least significant word)
    //Pad the array with leading zeros so that it has at least minSize elements.
    //There will always be at least one leading 0 element.
    function int2bigInt(t,bits,minSize) {
      var i,k;
      k=Math.ceil(bits/bpe)+1;
      k=minSize>k ? minSize : k;
      var buff=new Array(k);
      copyInt_(buff,t);
      return buff;
    }

    //return the bigInt given a string representation in a given base.
    //Pad the array with leading zeros so that it has at least minSize elements.
    //If base=-1, then it reads in a space-separated list of array elements in decimal.
    //The array will always have at least one leading zero, unless base=-1.
    function str2bigInt(s,b,minSize) {
      var d, i, j, base, str, x, y, kk;
      if (typeof b === 'string') {
          base = b.length;
          str = b;
      } else {
          base = b;
          str = digitsStr;
      }
      var k=s.length;
      if (base==-1) { //comma-separated list of array elements in decimal
        x=new Array(0);
        for (;;) {
          y=new Array(x.length+1);
          for (i=0;i<x.length;i++)
            y[i+1]=x[i];
          y[0]=parseInt(s,10);
          x=y;
          d=s.indexOf(',',0);
          if (d<1)
            break;
          s=s.substring(d+1);
          if (s.length==0)
            break;
        }
        if (x.length<minSize) {
          y=new Array(minSize);
          copy_(y,x);
          return y;
        }
        return x;
      }

      x=int2bigInt(0,base*k,0);
    for (i=0;i<k;i++) {
      d=str.indexOf(s.substring(i,i+1),0);
      if (base<=36 && d>=36) { //convert lowercase to uppercase if base<=36
        d-=26;
      }
      if (d>=base || d<0) {   //ignore illegal characters
      continue;
        }
        multInt_(x,base);
        addInt_(x,d);
      }

      for (k=x.length;k>0 && !x[k-1];k--); //strip off leading zeros
      k=minSize>k+1 ? minSize : k+1;
      y=new Array(k);
      kk=k<x.length ? k : x.length;
      for (i=0;i<kk;i++)
        y[i]=x[i];
      for (;i<k;i++)
        y[i]=0;
      return y;
    }

    //is bigint x equal to integer y?
    //y must have less than bpe bits
    function equalsInt(x,y) {
      var i;
      if (x[0]!=y)
        return 0;
      for (i=1;i<x.length;i++)
        if (x[i])
          return 0;
      return 1;
    }

    //are bigints x and y equal?
    //this works even if x and y are different lengths and have arbitrarily many leading zeros
    function equals(x,y) {
      var i;
      var k=x.length<y.length ? x.length : y.length;
      for (i=0;i<k;i++)
        if (x[i]!=y[i])
          return 0;
      if (x.length>y.length) {
        for (;i<x.length;i++)
          if (x[i])
            return 0;
      } else {
        for (;i<y.length;i++)
          if (y[i])
            return 0;
      }
      return 1;
    }

    //is the bigInt x equal to zero?
    function isZero(x) {
      var i;
      for (i=0;i<x.length;i++)
        if (x[i])
          return 0;
      return 1;
    }

    //convert a bigInt into a string in a given base, from base 2 up to base 95.
    //Base -1 prints the contents of the array representing the number.
    function bigInt2str(x,b) {
      var i,t,base,str,s="";
      if (typeof b === 'string') {
          base = b.length;
          str = b;
      } else {
          base = b;
          str = digitsStr;
      }

      if (s6.length!=x.length)
        s6=dup(x);
      else
        copy_(s6,x);

      if (base==-1) { //return the list of array contents
        for (i=x.length-1;i>0;i--)
          s+=x[i]+',';
        s+=x[0];
      }
      else { //return it in the given base
        while (!isZero(s6)) {
          t=divInt_(s6,base);  //t=s6 % base; s6=floor(s6/base);
      s=str.substring(t,t+1)+s;
        }
      }
      if (s.length==0)
    s=str[0];
      return s;
    }

    //returns a duplicate of bigInt x
    function dup(x) {
      var i;
      var buff=new Array(x.length);
      copy_(buff,x);
      return buff;
    }

    //do x=y on bigInts x and y.  x must be an array at least as big as y (not counting the leading zeros in y).
    function copy_(x,y) {
      var i;
      var k=x.length<y.length ? x.length : y.length;
      for (i=0;i<k;i++)
        x[i]=y[i];
      for (i=k;i<x.length;i++)
        x[i]=0;
    }

    //do x=y on bigInt x and integer y.
    function copyInt_(x,n) {
      var i,c;
      for (c=n,i=0;i<x.length;i++) {
        x[i]=c & mask;
        c>>=bpe;
      }
    }

    //do x=x+n where x is a bigInt and n is an integer.
    //x must be large enough to hold the result.
    function addInt_(x,n) {
      var i,k,c,b;
      x[0]+=n;
      k=x.length;
      c=0;
      for (i=0;i<k;i++) {
        c+=x[i];
        b=0;
        if (c<0) {
          b=-(c>>bpe);
          c+=b*radix;
        }
        x[i]=c & mask;
        c=(c>>bpe)-b;
        if (!c) return; //stop carrying as soon as the carry is zero
      }
    }

    //right shift bigInt x by n bits.  0 <= n < bpe.
    function rightShift_(x,n) {
      var i;
      var k=Math.floor(n/bpe);
      if (k) {
        for (i=0;i<x.length-k;i++) //right shift x by k elements
          x[i]=x[i+k];
        for (;i<x.length;i++)
          x[i]=0;
        n%=bpe;
      }
      for (i=0;i<x.length-1;i++) {
        x[i]=mask & ((x[i+1]<<(bpe-n)) | (x[i]>>n));
      }
      x[i]>>=n;
    }

    //do x=floor(|x|/2)*sgn(x) for bigInt x in 2's complement
    function halve_(x) {
      var i;
      for (i=0;i<x.length-1;i++) {
        x[i]=mask & ((x[i+1]<<(bpe-1)) | (x[i]>>1));
      }
      x[i]=(x[i]>>1) | (x[i] & (radix>>1));  //most significant bit stays the same
    }

    //left shift bigInt x by n bits.
    function leftShift_(x,n) {
      var i;
      var k=Math.floor(n/bpe);
      if (k) {
        for (i=x.length; i>=k; i--) //left shift x by k elements
          x[i]=x[i-k];
        for (;i>=0;i--)
          x[i]=0;
        n%=bpe;
      }
      if (!n)
        return;
      for (i=x.length-1;i>0;i--) {
        x[i]=mask & ((x[i]<<n) | (x[i-1]>>(bpe-n)));
      }
      x[i]=mask & (x[i]<<n);
    }

    //do x=x*n where x is a bigInt and n is an integer.
    //x must be large enough to hold the result.
    function multInt_(x,n) {
      var i,k,c,b;
      if (!n)
        return;
      k=x.length;
      c=0;
      for (i=0;i<k;i++) {
        c+=x[i]*n;
        b=0;
        if (c<0) {
          b=-(c>>bpe);
          c+=b*radix;
        }
        x[i]=c & mask;
        c=(c>>bpe)-b;
      }
    }

    //do x=floor(x/n) for bigInt x and integer n, and return the remainder
    function divInt_(x,n) {
      var i,r=0,s;
      for (i=x.length-1;i>=0;i--) {
        s=r*radix+x[i];
        x[i]=Math.floor(s/n);
        r=s%n;
      }
      return r;
    }

    //do the linear combination x=a*x+b*y for bigInts x and y, and integers a and b.
    //x must be large enough to hold the answer.
    function linComb_(x,y,a,b) {
      var i,c,k,kk;
      k=x.length<y.length ? x.length : y.length;
      kk=x.length;
      for (c=0,i=0;i<k;i++) {
        c+=a*x[i]+b*y[i];
        x[i]=c & mask;
        c>>=bpe;
      }
      for (i=k;i<kk;i++) {
        c+=a*x[i];
        x[i]=c & mask;
        c>>=bpe;
      }
    }

    //do the linear combination x=a*x+b*(y<<(ys*bpe)) for bigInts x and y, and integers a, b and ys.
    //x must be large enough to hold the answer.
    function linCombShift_(x,y,b,ys) {
      var i,c,k,kk;
      k=x.length<ys+y.length ? x.length : ys+y.length;
      kk=x.length;
      for (c=0,i=ys;i<k;i++) {
        c+=x[i]+b*y[i-ys];
        x[i]=c & mask;
        c>>=bpe;
      }
      for (i=k;c && i<kk;i++) {
        c+=x[i];
        x[i]=c & mask;
        c>>=bpe;
      }
    }

    //do x=x+(y<<(ys*bpe)) for bigInts x and y, and integer ys.
    //x must be large enough to hold the answer.
    function addShift_(x,y,ys) {
      var i,c,k,kk;
      k=x.length<ys+y.length ? x.length : ys+y.length;
      kk=x.length;
      for (c=0,i=ys;i<k;i++) {
        c+=x[i]+y[i-ys];
        x[i]=c & mask;
        c>>=bpe;
      }
      for (i=k;c && i<kk;i++) {
        c+=x[i];
        x[i]=c & mask;
        c>>=bpe;
      }
    }

    //do x=x-(y<<(ys*bpe)) for bigInts x and y, and integer ys.
    //x must be large enough to hold the answer.
    function subShift_(x,y,ys) {
      var i,c,k,kk;
      k=x.length<ys+y.length ? x.length : ys+y.length;
      kk=x.length;
      for (c=0,i=ys;i<k;i++) {
        c+=x[i]-y[i-ys];
        x[i]=c & mask;
        c>>=bpe;
      }
      for (i=k;c && i<kk;i++) {
        c+=x[i];
        x[i]=c & mask;
        c>>=bpe;
      }
    }

    //do x=x-y for bigInts x and y.
    //x must be large enough to hold the answer.
    //negative answers will be 2s complement
    function sub_(x,y) {
      var i,c,k,kk;
      k=x.length<y.length ? x.length : y.length;
      for (c=0,i=0;i<k;i++) {
        c+=x[i]-y[i];
        x[i]=c & mask;
        c>>=bpe;
      }
      for (i=k;c && i<x.length;i++) {
        c+=x[i];
        x[i]=c & mask;
        c>>=bpe;
      }
    }

    //do x=x+y for bigInts x and y.
    //x must be large enough to hold the answer.
    function add_(x,y) {
      var i,c,k,kk;
      k=x.length<y.length ? x.length : y.length;
      for (c=0,i=0;i<k;i++) {
        c+=x[i]+y[i];
        x[i]=c & mask;
        c>>=bpe;
      }
      for (i=k;c && i<x.length;i++) {
        c+=x[i];
        x[i]=c & mask;
        c>>=bpe;
      }
    }

    //do x=x*y for bigInts x and y.  This is faster when y<x.
    function mult_(x,y) {
      var i;
      if (ss.length!=2*x.length)
        ss=new Array(2*x.length);
      copyInt_(ss,0);
      for (i=0;i<y.length;i++)
        if (y[i])
          linCombShift_(ss,x,y[i],i);   //ss=1*ss+y[i]*(x<<(i*bpe))
      copy_(x,ss);
    }

    //do x=x mod n for bigInts x and n.
    function mod_(x,n) {
      if (s4.length!=x.length)
        s4=dup(x);
      else
        copy_(s4,x);
      if (s5.length!=x.length)
        s5=dup(x);
      divide_(s4,n,s5,x);  //x = remainder of s4 / n
    }

    //do x=x*y mod n for bigInts x,y,n.
    //for greater speed, let y<x.
    function multMod_(x,y,n) {
      var i;
      if (s0.length!=2*x.length)
        s0=new Array(2*x.length);
      copyInt_(s0,0);
      for (i=0;i<y.length;i++)
        if (y[i])
          linCombShift_(s0,x,y[i],i);   //s0=1*s0+y[i]*(x<<(i*bpe))
      mod_(s0,n);
      copy_(x,s0);
    }

    //do x=x*x mod n for bigInts x,n.
    function squareMod_(x,n) {
      var i,j,d,c,kx,kn,k;
      for (kx=x.length; kx>0 && !x[kx-1]; kx--);  //ignore leading zeros in x
      k=kx>n.length ? 2*kx : 2*n.length; //k=# elements in the product, which is twice the elements in the larger of x and n
      if (s0.length!=k)
        s0=new Array(k);
      copyInt_(s0,0);
      for (i=0;i<kx;i++) {
        c=s0[2*i]+x[i]*x[i];
        s0[2*i]=c & mask;
        c>>=bpe;
        for (j=i+1;j<kx;j++) {
          c=s0[i+j]+2*x[i]*x[j]+c;
          s0[i+j]=(c & mask);
          c>>=bpe;
        }
        s0[i+kx]=c;
      }
      mod_(s0,n);
      copy_(x,s0);
    }

    //return x with exactly k leading zero elements
    function trim(x,k) {
      var i,y;
      for (i=x.length; i>0 && !x[i-1]; i--);
      y=new Array(i+k);
      copy_(y,x);
      return y;
    }

    //do x=x**y mod n, where x,y,n are bigInts and ** is exponentiation.  0**0=1.
    //this is faster when n is odd.  x usually needs to have as many elements as n.
    function powMod_(x,y,n) {
      var k1,k2,kn,np;
      if(s7.length!=n.length)
        s7=dup(n);

      //for even modulus, use a simple square-and-multiply algorithm,
      //rather than using the more complex Montgomery algorithm.
      if ((n[0]&1)==0) {
        copy_(s7,x);
        copyInt_(x,1);
        while(!equalsInt(y,0)) {
          if (y[0]&1)
            multMod_(x,s7,n);
          divInt_(y,2);
          squareMod_(s7,n);
        }
        return;
      }

      //calculate np from n for the Montgomery multiplications
      copyInt_(s7,0);
      for (kn=n.length;kn>0 && !n[kn-1];kn--);
      np=radix-inverseModInt(modInt(n,radix),radix);
      s7[kn]=1;
      multMod_(x ,s7,n);   // x = x * 2**(kn*bp) mod n

      if (s3.length!=x.length)
        s3=dup(x);
      else
        copy_(s3,x);

      for (k1=y.length-1;k1>0 & !y[k1]; k1--);  //k1=first nonzero element of y
      if (y[k1]==0) {  //anything to the 0th power is 1
        copyInt_(x,1);
        return;
      }
      for (k2=1<<(bpe-1);k2 && !(y[k1] & k2); k2>>=1);  //k2=position of first 1 bit in y[k1]
      for (;;) {
        if (!(k2>>=1)) {  //look at next bit of y
          k1--;
          if (k1<0) {
            mont_(x,one,n,np);
            return;
          }
          k2=1<<(bpe-1);
        }
        mont_(x,x,n,np);

        if (k2 & y[k1]) //if next bit is a 1
          mont_(x,s3,n,np);
      }
    }


    //do x=x*y*Ri mod n for bigInts x,y,n,
    //  where Ri = 2**(-kn*bpe) mod n, and kn is the
    //  number of elements in the n array, not
    //  counting leading zeros.
    //x array must have at least as many elemnts as the n array
    //It's OK if x and y are the same variable.
    //must have:
    //  x,y < n
    //  n is odd
    //  np = -(n^(-1)) mod radix
    function mont_(x,y,n,np) {
      var i,j,c,ui,t,ks;
      var kn=n.length;
      var ky=y.length;

      if (sa.length!=kn)
        sa=new Array(kn);

      copyInt_(sa,0);

      for (;kn>0 && n[kn-1]==0;kn--); //ignore leading zeros of n
      for (;ky>0 && y[ky-1]==0;ky--); //ignore leading zeros of y
      ks=sa.length-1; //sa will never have more than this many nonzero elements.

      //the following loop consumes 95% of the runtime for randTruePrime_() and powMod_() for large numbers
      for (i=0; i<kn; i++) {
        t=sa[0]+x[i]*y[0];
        ui=((t & mask) * np) & mask;  //the inner "& mask" was needed on Safari (but not MSIE) at one time
        c=(t+ui*n[0]) >> bpe;
        t=x[i];

        //do sa=(sa+x[i]*y+ui*n)/b   where b=2**bpe.  Loop is unrolled 5-fold for speed
        j=1;
        for (;j<ky-4;) { c+=sa[j]+ui*n[j]+t*y[j];   sa[j-1]=c & mask;   c>>=bpe;   j++;
                         c+=sa[j]+ui*n[j]+t*y[j];   sa[j-1]=c & mask;   c>>=bpe;   j++;
                         c+=sa[j]+ui*n[j]+t*y[j];   sa[j-1]=c & mask;   c>>=bpe;   j++;
                         c+=sa[j]+ui*n[j]+t*y[j];   sa[j-1]=c & mask;   c>>=bpe;   j++;
                         c+=sa[j]+ui*n[j]+t*y[j];   sa[j-1]=c & mask;   c>>=bpe;   j++; }
        for (;j<ky;)   { c+=sa[j]+ui*n[j]+t*y[j];   sa[j-1]=c & mask;   c>>=bpe;   j++; }
        for (;j<kn-4;) { c+=sa[j]+ui*n[j];          sa[j-1]=c & mask;   c>>=bpe;   j++;
                         c+=sa[j]+ui*n[j];          sa[j-1]=c & mask;   c>>=bpe;   j++;
                         c+=sa[j]+ui*n[j];          sa[j-1]=c & mask;   c>>=bpe;   j++;
                         c+=sa[j]+ui*n[j];          sa[j-1]=c & mask;   c>>=bpe;   j++;
                         c+=sa[j]+ui*n[j];          sa[j-1]=c & mask;   c>>=bpe;   j++; }
        for (;j<kn;)   { c+=sa[j]+ui*n[j];          sa[j-1]=c & mask;   c>>=bpe;   j++; }
        for (;j<ks;)   { c+=sa[j];                  sa[j-1]=c & mask;   c>>=bpe;   j++; }
        sa[j-1]=c & mask;
      }

      if (!greater(n,sa))
        sub_(sa,n);
      copy_(x,sa);
    }

    module.exports = {
        'add': add,
        'addInt': addInt,
        'bigInt2str': bigInt2str,
        'bitSize': bitSize,
        'dup': dup,
        'equals': equals,
        'equalsInt': equalsInt,
        'expand': expand,
        'findPrimes': findPrimes,
        'GCD': GCD,
        'greater': greater,
        'greaterShift': greaterShift,
        'int2bigInt': int2bigInt,
        'inverseMod': inverseMod,
        'inverseModInt': inverseModInt,
        'isZero': isZero,
        'millerRabin': millerRabin,
        'millerRabinInt': millerRabinInt,
        'mod': mod,
        'modInt': modInt,
        'mult': mult,
        'multMod': multMod,
        'negative': negative,
        'powMod': powMod,
        'randBigInt': randBigInt,
        'randTruePrime': randTruePrime,
        'randProbPrime': randProbPrime,
        'str2bigInt': str2bigInt,
        'sub': sub,
        'trim': trim,
        'addInt_': addInt_,
        'add_': add_,
        'copy_': copy_,
        'copyInt_': copyInt_,
        'GCD_': GCD_,
        'inverseMod_': inverseMod_,
        'mod_': mod_,
        'mult_': mult_,
        'multMod_': multMod_,
        'powMod_': powMod_,
        'randBigInt_': randBigInt_,
        'randTruePrime_': randTruePrime_,
        'sub_': sub_,
        'addShift_': addShift_,
        'carry_': carry_,
        'divide_': divide_,
        'divInt_': divInt_,
        'eGCD_': eGCD_,
        'halve_': halve_,
        'leftShift_': leftShift_,
        'linComb_': linComb_,
        'linCombShift_': linCombShift_,
        'mont_': mont_,
        'multInt_': multInt_,
        'rightShift_': rightShift_,
        'squareMod_': squareMod_,
        'subShift_': subShift_,
    };

});

/**
 * [js-sha256]{@link https://github.com/emn178/js-sha256}
 *
 * @version 0.3.2
 * @author Chen, Yi-Cyuan [emn178@gmail.com]
 * @copyright Chen, Yi-Cyuan 2014-2016
 * @license MIT
 */
(function (root) {
    'use strict';
  
    var NODE_JS = typeof process == 'object' && process.versions && process.versions.node;
    if (NODE_JS) {
      root = global;
    }
    var COMMON_JS = !root.JS_SHA256_TEST && typeof module == 'object' && module.exports;
    var HEX_CHARS = '0123456789abcdef'.split('');
    var EXTRA = [-2147483648, 8388608, 32768, 128];
    var SHIFT = [24, 16, 8, 0];
    var K =[0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
            0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
            0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
            0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
            0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
            0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
            0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
            0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2];
  
    var blocks = [];
  
    var sha224 = function (message) {
      return sha256(message, true);
    };
  
    var sha256 = function (message, is224) {
      var notString = typeof message != 'string';
      if (notString && message.constructor == root.ArrayBuffer) {
        message = new Uint8Array(message);
      }
  
      var h0, h1, h2, h3, h4, h5, h6, h7, block, code, first = true, end = false,
          i, j, index = 0, start = 0, bytes = 0, length = message.length,
          s0, s1, maj, t1, t2, ch, ab, da, cd, bc;
  
      if (is224) {
        h0 = 0xc1059ed8;
        h1 = 0x367cd507;
        h2 = 0x3070dd17;
        h3 = 0xf70e5939;
        h4 = 0xffc00b31;
        h5 = 0x68581511;
        h6 = 0x64f98fa7;
        h7 = 0xbefa4fa4;
      } else { // 256
        h0 = 0x6a09e667;
        h1 = 0xbb67ae85;
        h2 = 0x3c6ef372;
        h3 = 0xa54ff53a;
        h4 = 0x510e527f;
        h5 = 0x9b05688c;
        h6 = 0x1f83d9ab;
        h7 = 0x5be0cd19;
      }
      block = 0;
      do {
        blocks[0] = block;
        blocks[16] = blocks[1] = blocks[2] = blocks[3] =
        blocks[4] = blocks[5] = blocks[6] = blocks[7] =
        blocks[8] = blocks[9] = blocks[10] = blocks[11] =
        blocks[12] = blocks[13] = blocks[14] = blocks[15] = 0;
        if (notString) {
          for (i = start;index < length && i < 64;++index) {
            blocks[i >> 2] |= message[index] << SHIFT[i++ & 3];
          }
        } else {
          for (i = start;index < length && i < 64;++index) {
            code = message.charCodeAt(index);
            if (code < 0x80) {
              blocks[i >> 2] |= code << SHIFT[i++ & 3];
            } else if (code < 0x800) {
              blocks[i >> 2] |= (0xc0 | (code >> 6)) << SHIFT[i++ & 3];
              blocks[i >> 2] |= (0x80 | (code & 0x3f)) << SHIFT[i++ & 3];
            } else if (code < 0xd800 || code >= 0xe000) {
              blocks[i >> 2] |= (0xe0 | (code >> 12)) << SHIFT[i++ & 3];
              blocks[i >> 2] |= (0x80 | ((code >> 6) & 0x3f)) << SHIFT[i++ & 3];
              blocks[i >> 2] |= (0x80 | (code & 0x3f)) << SHIFT[i++ & 3];
            } else {
              code = 0x10000 + (((code & 0x3ff) << 10) | (message.charCodeAt(++index) & 0x3ff));
              blocks[i >> 2] |= (0xf0 | (code >> 18)) << SHIFT[i++ & 3];
              blocks[i >> 2] |= (0x80 | ((code >> 12) & 0x3f)) << SHIFT[i++ & 3];
              blocks[i >> 2] |= (0x80 | ((code >> 6) & 0x3f)) << SHIFT[i++ & 3];
              blocks[i >> 2] |= (0x80 | (code & 0x3f)) << SHIFT[i++ & 3];
            }
          }
        }
        bytes += i - start;
        start = i - 64;
        if (index == length) {
          blocks[i >> 2] |= EXTRA[i & 3];
          ++index;
        }
        block = blocks[16];
        if (index > length && i < 56) {
          blocks[15] = bytes << 3;
          end = true;
        }
  
        var a = h0, b = h1, c = h2, d = h3, e = h4, f = h5, g = h6, h = h7;
        for (j = 16;j < 64;++j) {
          // rightrotate
          t1 = blocks[j - 15];
          s0 = ((t1 >>> 7) | (t1 << 25)) ^ ((t1 >>> 18) | (t1 << 14)) ^ (t1 >>> 3);
          t1 = blocks[j - 2];
          s1 = ((t1 >>> 17) | (t1 << 15)) ^ ((t1 >>> 19) | (t1 << 13)) ^ (t1 >>> 10);
          blocks[j] = blocks[j - 16] + s0 + blocks[j - 7] + s1 << 0;
        }
  
        bc = b & c;
        for (j = 0;j < 64;j += 4) {
          if (first) {
            if (is224) {
              ab = 300032;
              t1 = blocks[0] - 1413257819;
              h = t1 - 150054599 << 0;
              d = t1 + 24177077 << 0;
            } else {
              ab = 704751109;
              t1 = blocks[0] - 210244248;
              h = t1 - 1521486534 << 0;
              d = t1 + 143694565 << 0;
            }
            first = false;
          } else {
            s0 = ((a >>> 2) | (a << 30)) ^ ((a >>> 13) | (a << 19)) ^ ((a >>> 22) | (a << 10));
            s1 = ((e >>> 6) | (e << 26)) ^ ((e >>> 11) | (e << 21)) ^ ((e >>> 25) | (e << 7));
            ab = a & b;
            maj = ab ^ (a & c) ^ bc;
            ch = (e & f) ^ (~e & g);
            t1 = h + s1 + ch + K[j] + blocks[j];
            t2 = s0 + maj;
            h = d + t1 << 0;
            d = t1 + t2 << 0;
          }
          s0 = ((d >>> 2) | (d << 30)) ^ ((d >>> 13) | (d << 19)) ^ ((d >>> 22) | (d << 10));
          s1 = ((h >>> 6) | (h << 26)) ^ ((h >>> 11) | (h << 21)) ^ ((h >>> 25) | (h << 7));
          da = d & a;
          maj = da ^ (d & b) ^ ab;
          ch = (h & e) ^ (~h & f);
          t1 = g + s1 + ch + K[j + 1] + blocks[j + 1];
          t2 = s0 + maj;
          g = c + t1 << 0;
          c = t1 + t2 << 0;
          s0 = ((c >>> 2) | (c << 30)) ^ ((c >>> 13) | (c << 19)) ^ ((c >>> 22) | (c << 10));
          s1 = ((g >>> 6) | (g << 26)) ^ ((g >>> 11) | (g << 21)) ^ ((g >>> 25) | (g << 7));
          cd = c & d;
          maj = cd ^ (c & a) ^ da;
          ch = (g & h) ^ (~g & e);
          t1 = f + s1 + ch + K[j + 2] + blocks[j + 2];
          t2 = s0 + maj;
          f = b + t1 << 0;
          b = t1 + t2 << 0;
          s0 = ((b >>> 2) | (b << 30)) ^ ((b >>> 13) | (b << 19)) ^ ((b >>> 22) | (b << 10));
          s1 = ((f >>> 6) | (f << 26)) ^ ((f >>> 11) | (f << 21)) ^ ((f >>> 25) | (f << 7));
          bc = b & c;
          maj = bc ^ (b & d) ^ cd;
          ch = (f & g) ^ (~f & h);
          t1 = e + s1 + ch + K[j + 3] + blocks[j + 3];
          t2 = s0 + maj;
          e = a + t1 << 0;
          a = t1 + t2 << 0;
        }
  
        h0 = h0 + a << 0;
        h1 = h1 + b << 0;
        h2 = h2 + c << 0;
        h3 = h3 + d << 0;
        h4 = h4 + e << 0;
        h5 = h5 + f << 0;
        h6 = h6 + g << 0;
        h7 = h7 + h << 0;
      } while (!end);
  
      var hex = HEX_CHARS[(h0 >> 28) & 0x0F] + HEX_CHARS[(h0 >> 24) & 0x0F] +
                HEX_CHARS[(h0 >> 20) & 0x0F] + HEX_CHARS[(h0 >> 16) & 0x0F] +
                HEX_CHARS[(h0 >> 12) & 0x0F] + HEX_CHARS[(h0 >> 8) & 0x0F] +
                HEX_CHARS[(h0 >> 4) & 0x0F] + HEX_CHARS[h0 & 0x0F] +
                HEX_CHARS[(h1 >> 28) & 0x0F] + HEX_CHARS[(h1 >> 24) & 0x0F] +
                HEX_CHARS[(h1 >> 20) & 0x0F] + HEX_CHARS[(h1 >> 16) & 0x0F] +
                HEX_CHARS[(h1 >> 12) & 0x0F] + HEX_CHARS[(h1 >> 8) & 0x0F] +
                HEX_CHARS[(h1 >> 4) & 0x0F] + HEX_CHARS[h1 & 0x0F] +
                HEX_CHARS[(h2 >> 28) & 0x0F] + HEX_CHARS[(h2 >> 24) & 0x0F] +
                HEX_CHARS[(h2 >> 20) & 0x0F] + HEX_CHARS[(h2 >> 16) & 0x0F] +
                HEX_CHARS[(h2 >> 12) & 0x0F] + HEX_CHARS[(h2 >> 8) & 0x0F] +
                HEX_CHARS[(h2 >> 4) & 0x0F] + HEX_CHARS[h2 & 0x0F] +
                HEX_CHARS[(h3 >> 28) & 0x0F] + HEX_CHARS[(h3 >> 24) & 0x0F] +
                HEX_CHARS[(h3 >> 20) & 0x0F] + HEX_CHARS[(h3 >> 16) & 0x0F] +
                HEX_CHARS[(h3 >> 12) & 0x0F] + HEX_CHARS[(h3 >> 8) & 0x0F] +
                HEX_CHARS[(h3 >> 4) & 0x0F] + HEX_CHARS[h3 & 0x0F] +
                HEX_CHARS[(h4 >> 28) & 0x0F] + HEX_CHARS[(h4 >> 24) & 0x0F] +
                HEX_CHARS[(h4 >> 20) & 0x0F] + HEX_CHARS[(h4 >> 16) & 0x0F] +
                HEX_CHARS[(h4 >> 12) & 0x0F] + HEX_CHARS[(h4 >> 8) & 0x0F] +
                HEX_CHARS[(h4 >> 4) & 0x0F] + HEX_CHARS[h4 & 0x0F] +
                HEX_CHARS[(h5 >> 28) & 0x0F] + HEX_CHARS[(h5 >> 24) & 0x0F] +
                HEX_CHARS[(h5 >> 20) & 0x0F] + HEX_CHARS[(h5 >> 16) & 0x0F] +
                HEX_CHARS[(h5 >> 12) & 0x0F] + HEX_CHARS[(h5 >> 8) & 0x0F] +
                HEX_CHARS[(h5 >> 4) & 0x0F] + HEX_CHARS[h5 & 0x0F] +
                HEX_CHARS[(h6 >> 28) & 0x0F] + HEX_CHARS[(h6 >> 24) & 0x0F] +
                HEX_CHARS[(h6 >> 20) & 0x0F] + HEX_CHARS[(h6 >> 16) & 0x0F] +
                HEX_CHARS[(h6 >> 12) & 0x0F] + HEX_CHARS[(h6 >> 8) & 0x0F] +
                HEX_CHARS[(h6 >> 4) & 0x0F] + HEX_CHARS[h6 & 0x0F];
      if (!is224) {
        hex += HEX_CHARS[(h7 >> 28) & 0x0F] + HEX_CHARS[(h7 >> 24) & 0x0F] +
               HEX_CHARS[(h7 >> 20) & 0x0F] + HEX_CHARS[(h7 >> 16) & 0x0F] +
               HEX_CHARS[(h7 >> 12) & 0x0F] + HEX_CHARS[(h7 >> 8) & 0x0F] +
               HEX_CHARS[(h7 >> 4) & 0x0F] + HEX_CHARS[h7 & 0x0F];
      }
      return hex;
    };
    
    if (COMMON_JS) {
      sha256.sha256 = sha256;
      sha256.sha224 = sha224;
      module.exports = sha256;
    } else if (root) {
      root.sha256 = sha256;
      root.sha224 = sha224;
    }
  }(this));

(function (root, factory) {
    if (typeof define === 'function' && define.amd) {
      // AMD
      define(['exports'], factory);
    } else if (typeof exports === 'object' && typeof exports.nodeName !== 'string') {
      // Node, CommonJS-like
      factory(module.exports);
    } else {
      factory(root);
    }
  })(this, function (exports) {
  
      var srp = function(){
          this.n_base64 = "dadfccb918e5f651d7a1b851efab43f2c17068c69013e37033347e8da75ca8d8370c26c4fbf1a4aaa4afd9b5ab32343749ee4fbf6fa279856fd7c3ade30ecf2b";
          this.g = "2";
          this.hash_alg = "sha256";
          this.k = this.hash(this.n_base64 + this.g);
          this.rand_length = 128;
      }
  
      srp.prototype.generateX = function(s, username, password){
              var s = this.base2BigInt(s);
              s = this.bigIntToStr(s);
              var x = this.hash(s + this.hash(username + ":" + password));
  
              return x;
          }
  
       srp.prototype.generateV = function(x){
           var g = BigInt.str2bigInt(this.g, 10);
           var n = this.base2BigInt(this.n_base64);
           var x = this.base2BigInt(x);
           var v = this.bigIntToBase(BigInt.powMod(g, x, n));
  
           return v;
       }   
  
       srp.prototype.generateA = function(a){
           var g = BigInt.str2bigInt(this.g, 10);
           var n = this.base2BigInt(this.n_base64);
           var a = this.base2BigInt(a);
  
           var A = this.bigIntToBase(BigInt.powMod(g, a, n));
  
           return A;
       }
  
       srp.prototype.generateS_Client = function(A, B, a, x){
           var u = this.base2BigInt(this.generateU(A, B));
           var B = this.base2BigInt(B);
           var a = this.base2BigInt(a);
           var k = this.base2BigInt(this.k);
           var g = BigInt.str2bigInt(this.g, 10);
           var n = this.base2BigInt(this.n_base64);
           var x = this.base2BigInt(x);
  
           var S = this.bigIntToBase(BigInt.powMod(BigInt.sub(B, BigInt.mult(k, BigInt.powMod(g,x,n))),BigInt.add(a, BigInt.mult(u, x)), n));
  
           return S;
       }
  
  
        srp.prototype.generateB = function(b, v){
            var n = this.base2BigInt(this.n_base64);
            var v = this.base2BigInt(v);
            var b = this.base2BigInt(b);
            var k = this.base2BigInt(this.k);
            var g = BigInt.str2bigInt(this.g, 10);
  
            var B = this.bigIntToBase(BigInt.add(BigInt.mult(k,v), BigInt.powMod(g,b,n)));
  
            return B;
        }
  
      srp.prototype.generateS_Server = function(A,B,b,v){
          var u = this.base2BigInt(this.generateU(A, B));
          var n = this.base2BigInt(this.n_base64);
          var A = this.base2BigInt(A);
          var v = this.base2BigInt(v);
          var b = this.base2BigInt(b);
  
          var S = this.bigIntToBase(BigInt.powMod(BigInt.mult(A, BigInt.powMod(v,u,n)),b,n));
  
          return S;
      }
  
      srp.prototype.getRandomSeed = function(length){
          length = length ||this.rand_length;
  
          return this.bigIntToBase(BigInt.randBigInt(length * 4))
      }
  
      srp.prototype.generateU = function(A, B){
          return this.hash(A + B);
      }
  
      srp.prototype.generateM1 = function(A, B, S){
          return this.hash(A + B + S);
      }
  
  
      srp.prototype.generateM2 = function(A, M1, S){
          return this.hash(A + M1 + S);
      }
  
      srp.prototype.generateK = function(S){
          return this.hash(S);
      }
  
      srp.prototype.hash = function(value){
          if(this.hash_alg == "sha256"){
              return sha256(sha256(value));
          }
  
          throw "hash algorithm not supported";
          return null;
      }
  
      srp.prototype.base2BigInt = function(value, base){
          base = base || 16;
          return BigInt.str2bigInt(value, base);
      }
  
      srp.prototype.bigIntToStr = function(value){
          return BigInt.bigInt2str(value, 10)
      }
  
      srp.prototype.bigIntToBase = function(value, base){
          base = base || 16;
          return BigInt.bigInt2str(value, base).toLowerCase();
      }
  
      exports.srp = srp;
  });
  