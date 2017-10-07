using System;
using System.Diagnostics;
using System.Numerics;
using System.Reflection;
using System.Threading;
using System.Threading.Tasks;
using System.Threading.Algorithms;

using static System.Console;

namespace RSABigInt
{

    class MyBigInteger_Class
    {
        //const uint ARRAY_SIZE = 0x166e0e21;
        const uint ARRAY_SIZE = 0x10000000;
        Random _randObj;
        uint[] primes;               
        uint[] factor_base;          //
        uint[,] matrix;              // 2-dimensional matrix

        struct smooth_num
        {
            public BigInteger Q_of_x;
            public BigInteger x;
            public uint[] exponents;
        };
        smooth_num[] Qx;

        Stopwatch sw1 = new Stopwatch();

        /*
        public Random randObj
        {
            get { return _randObj; }
            set { _randObj = value; }
        }
         */

        // constructor
        public MyBigInteger_Class()
        {
            _randObj = new Random((int)DateTime.Now.Ticks);
            primes = new uint[ARRAY_SIZE];                  // 131072 elements --- 0x18000000 = 1.5GB array
            factor_base = new uint[ARRAY_SIZE];
        }

        public void prime_sieve(ulong n)
        {
            int p;
            primes.Initialize();

            sw1.Start();

            primes[0] = 2;
            for (p = 0; primes[p] <= n;) 
            {
                for (ulong i = primes[p]*primes[p]; i <= n; i+=primes[p])
                    primes[i] = 1;
                primes[++p] = primes[p-1] + 1;
                for (; primes[p] <= n && primes[primes[p]] == 1; primes[p]++) ; //find next prime (where s[p]==0)
            }
            Array.Resize(ref primes, p);

            sw1.Stop();
            string strElapsed;
            if (sw1.ElapsedMilliseconds <= 1000)
                strElapsed = String.Format("{0} ms", sw1.ElapsedMilliseconds);
            else
                strElapsed = String.Format("{0:F1} s", (float)sw1.ElapsedMilliseconds / 1000);

            WriteLine("prime_sieve time took: {0}", strElapsed);
        }

        BigInteger InverseMod(BigInteger x, BigInteger n)
        {
            if (x.IsEven && n.IsEven)       //if both inputs are even, then inverse doesn't exist
                return BigInteger.Zero;

            BigInteger eg_u = x;
            BigInteger eg_v = n;
            BigInteger eg_A = BigInteger.One;
            BigInteger eg_B = BigInteger.Zero;
            BigInteger eg_C = BigInteger.Zero;
            BigInteger eg_D = BigInteger.One;

            for (; ; )
            {
                while (eg_u.IsEven)      //while eg_u is even
                {
                    eg_u /= 2;
                    if (eg_A.IsEven && eg_B.IsEven)        //if eg_A==eg_B==0 are even
                    {
                        eg_A /= 2;
                        eg_B /= 2;
                    }
                    else
                    {
                        eg_A += n;
                        eg_A /= 2;
                        eg_B -= x;
                        eg_B /= 2;
                    }
                }   // while

                while (eg_v.IsEven)      //while eg_v is even
                {
                    eg_v /= 2;
                    if (eg_C.IsEven && eg_D.IsEven)         //if eg_C==eg_D==0 mod 2
                    {
                        eg_C /= 2;
                        eg_D /= 2;
                    }
                    else
                    {
                        eg_C += n;
                        eg_C /= 2;
                        eg_D -= x;
                        eg_D /= 2;
                    }
                }   // while

                if (eg_v <= eg_u)        //eg_v <= eg_u
                {
                    eg_u -= eg_v;
                    eg_A -= eg_C;
                    eg_B -= eg_D;
                }
                else
                {                        //eg_v > eg_u
                    eg_v -= eg_u;
                    eg_C -= eg_A;
                    eg_D -= eg_B;
                }

                if (eg_u == BigInteger.Zero)
                {
                    if (eg_C.Sign == -1)  //make sure answer is non-negative
                        eg_C += n;
                    x = eg_C;

                    if (eg_v != BigInteger.One)    //if GCD_(x,n)!=1, then there is no inverse
                        x = BigInteger.Zero;
                    return x;
                }
            }   // for
        }

        BigInteger RandPrime(int size)
        {
            BigInteger rand1 = BigInteger.Zero;
            BigInteger rem = BigInteger.Zero;
            BigInteger a = new BigInteger(2);

            while (!rem.IsOne)
            {
                rand1 = BigInteger.Zero;
                for (int i = 0; i < size; i++)
                {
                    rand1 <<= 24;
                    rand1 += _randObj.Next();
                }
                rand1 |= 1;

                rem = BigInteger.ModPow(a, rand1 - 1, rand1);
            }
            return rand1;
        }

        BigInteger TwinPrime(int size)
        {
            BigInteger twin = RandPrime(size);
            bool found = false;
            do
            {
                twin += 2;
                found = MillerRabin(twin, 2) && MillerRabin(twin + 2, 2);
            } while (!found);
            
            return twin;
        }

        BigInteger PrimeTriplet(int size)
        {
            BigInteger triple = RandPrime(size);
            bool found = false;
            do
            {
                if (MillerRabin(triple, 2))
                {
                    found = (MillerRabin(triple + 2, 2) || MillerRabin(triple + 4, 2)) 
                            && MillerRabin(triple + 6, 2);
                }

                if (!found)
                    triple += 2;

            } while (!found);

            return triple;
        }

        public BigInteger SquareRoot(BigInteger n)
        {
            BigInteger d = BigInteger.One, q;

            sw1.Restart();
            //Newton's Method
            do
            {
                q = n / d + d;
                q /= 2;
                d = q;
            } while (q*q > n);

            sw1.Stop();
            string strElapsed;
            if (sw1.ElapsedMilliseconds <= 1000)
                strElapsed = String.Format("{0} ms", sw1.ElapsedMilliseconds);
            else
                strElapsed = String.Format("{0:F1} s", (float)sw1.ElapsedMilliseconds / 1000);

            WriteLine("\nSquareRoot({0})\nElapsed time: {1}\n", n.ToString(), strElapsed);

            return q;
        }

        public BigInteger Factorial(int n)
        {
            BigInteger fact = BigInteger.One;

            sw1.Restart();
            for (int i = 2; i <= n; i++)
                fact *= i;

            sw1.Stop();
            string strElapsed;
            if (sw1.ElapsedMilliseconds <= 1000)
                strElapsed = String.Format("{0} ms", sw1.ElapsedMilliseconds);
            else
                strElapsed = String.Format("{0:F1} s", (float)sw1.ElapsedMilliseconds / 1000);

            WriteLine("\nFactorial() Elapsed time: {0}\n", strElapsed);

            return fact;
        }

        public BigInteger Fibonacci(int n)
        {
            BigInteger Fn = BigInteger.Zero;
            BigInteger Fn_plus_one = BigInteger.One;

            sw1.Restart();
            for (int i = 1; i < n; i++)
            {
                BigInteger fib_temp = Fn_plus_one;
                Fn_plus_one += Fn;
                Fn = fib_temp;
            }

            sw1.Stop();
            string strElapsed;
            if (sw1.ElapsedMilliseconds <= 1000)
                strElapsed = String.Format("{0} ms", sw1.ElapsedMilliseconds);
            else
                strElapsed = String.Format("{0:F1} s", (float)sw1.ElapsedMilliseconds / 1000);

            WriteLine("\nFactorial() Elapsed time: {0}\n", strElapsed);

            return Fn_plus_one;
        }

        uint[] GetPrimeFactors(BigInteger N)
        {
            uint [] factor_expos = new uint[factor_base.Length];

            for (uint i=0; i<factor_base.Length; i++)
            {
                uint j = 0;
                for (j = 0; (N % factor_base[i]) == 0; j++)
                    N /= factor_base[i];
                factor_expos[i] = j;
            }
            if (N == 1)
                return factor_expos;
            else
                return null;
        }

        void Factor_Base(BigInteger N)
        {
            int j = 0;
            for (int i = 0; i < primes.Length; i++)
                if (Legendre(N, primes[i]) == 1)
                {
                    //Write(factor_base[j] + "\t  ");
                    factor_base[j++] = primes[i];
                }
            Array.Resize(ref factor_base, j);
            WriteLine("Factor base: {0} primes.\n", j);
        }

        public void Smooth_Numbers(BigInteger N1)
        {
            BigInteger sqrt_N1 = SquareRoot(N1);
            BigInteger i = sqrt_N1 + 1;
            BigInteger j = sqrt_N1 - 1;

            // Collect smooth numbers
            Factor_Base(N1);

            uint N_smooths = (uint)(factor_base.Length * 1.1);
            if ((N_smooths & 1) == 1)
                N_smooths++;                // make it even
            Qx = new smooth_num[N_smooths];
            Qx.Initialize();
            long k = -1;
            sw1.Restart();

            Task[] smooth = new Task[2];
            smooth[0] = Task.Run(() =>
            {
                while (k < N_smooths-1)
                {
                    BigInteger sm = i * i - N1;
                    uint[] expo1 = GetPrimeFactors(sm);
                    if (expo1 != null)
                    {
                        Interlocked.Increment(ref k); 
                        Qx[k].Q_of_x = sm;
                        Qx[k].x = i;
                        Qx[k].exponents = expo1;

                        Write(k.ToString() + " smooth numbers\r");
                    }
                    i++;
                    /*
                    sm = N1 - j * j;
                    expo1 = GetPrimeFactors(sm);
                    if (expo1 != null)
                    {
                        Qx[k].Q_of_x = sm;
                        Qx[k].x = j;
                        Qx[k].exponents = expo1;
                        Interlocked.Increment(ref k);
                        Write(k.ToString() + " smooth numbers\r");
                    }
                    j--;
                     */ 
                }
            });

            smooth[1] = Task.Run(() =>
            {
                while (k < N_smooths-1)
                {
                    BigInteger sm = N1 - j * j;
                    uint[] expo1 = GetPrimeFactors(sm);
                    if (expo1 != null)
                    {
                        Interlocked.Increment(ref k); 
                        Qx[k].Q_of_x = sm;
                        Qx[k].x = j;
                        Qx[k].exponents = expo1;
                        Write(k.ToString() + " smooth numbers\r");
                    }
                    j--;
                }
            });

            Task.WaitAll(smooth);
            
            sw1.Stop();
            string strElapsed;
            if (sw1.ElapsedMilliseconds <= 1000)
                strElapsed = String.Format("{0} ms", sw1.ElapsedMilliseconds);
            else
                strElapsed = String.Format("{0:F1} s", (float)sw1.ElapsedMilliseconds / 1000);
            
            WriteLine("Collected {0} smooth numbers.\nElapsed time: {1}\n", k, strElapsed);
            //WriteLine("{0}\t{1}", i - sqrt_N1, sqrt_N1 - j);
        }

        public void Smooth_Numbers2(BigInteger N1)
        {
            BigInteger sqrt_N1 = SquareRoot(N1);
            BigInteger i = sqrt_N1 + 1;
            BigInteger j = sqrt_N1 - 1;

            // prime number factors
            Factor_Base(N1);
            uint N_smooths = (uint)(factor_base.Length * 1.1);
            if ( (N_smooths & 1) == 1)
                N_smooths++;                // make it even
            Qx = new smooth_num[N_smooths];
            Qx.Initialize();
            
            smooth_num[] Q1x = new smooth_num[N_smooths];
            Q1x.Initialize();

            long k = 0;
            sw1.Restart();

            // Collect smooth numbers
            while (k < N_smooths)
            {
                uint n = 0;
                while (n < Q1x.Length)
                {
                    Q1x[n].Q_of_x = N1 - j * j;
                    Q1x[n].x = j;
                    j--;
                    n++;

                    Q1x[n].Q_of_x = i * i - N1;
                    Q1x[n].x = i;
                    i++;
                    n++;
                }

                CancellationTokenSource cancellationSource = new CancellationTokenSource();
                ParallelOptions options = new ParallelOptions();
                options.CancellationToken = cancellationSource.Token;
                Parallel.For(0, Q1x.Length, options, (ii, loopState) =>
                        {
                            uint[] expo1 = GetPrimeFactors(Q1x[ii].Q_of_x);
                            try
                            {
                                if (expo1 != null)
                                {
                                    Qx[k].Q_of_x = Q1x[ii].Q_of_x;      // save the smooth number 
                                    Qx[k].x = Q1x[ii].x;                // save the square root
                                    Qx[k].exponents = expo1;            // save the prime exponents
                                    Interlocked.Increment(ref k);
                                }
                            }
                            catch (IndexOutOfRangeException e)
                            {
                                loopState.Stop();
                            }
                        }
                );
                Write(k.ToString() + " smooth numbers\r");
            }   // while (k < factor_base.Length) 

            sw1.Stop();
            string strElapsed;
            if (sw1.ElapsedMilliseconds <= 1000)
                strElapsed = String.Format("{0} ms", sw1.ElapsedMilliseconds);
            else
                strElapsed = String.Format("{0:F1} s", (float)sw1.ElapsedMilliseconds / 1000);

            WriteLine("Collected {0} smooth numbers.\nElapsed time: {1}\n", k, strElapsed);
        }

        int Legendre(BigInteger n, uint p)
        {
            BigInteger p1, l;
    
            // assumes p is an odd prime
            p1 = (p-1)/2;
            l = BigInteger.ModPow(n, p1, p);
    
            if (l == 1)
                return 1;
            if (l == 0)
                return 0;
            else
                return -1;
        }

        bool MillerRabin(BigInteger n, int k)
        {
            int[] base_primes = 	{  2,   3,   5,   7,  11,  13,  17,  19,
	                                  23,  29,  31,  37,  41,  43,  47,  53,
	                                  59,  61,  67,  71,  73,  79,  83,  89,
	                                  97, 101, 103, 107, 109, 113, 127, 131,
	                                 137, 139, 149, 151, 157, 163, 167, 173,
	                                 179, 181, 191, 193, 197, 199, 211, 223,
	                                 227, 229, 233, 239, 241, 251};
            BigInteger r = n - 1;
            int s = 0;

            for (int i = 1; i < base_primes.Length; i++ )
                if (n % base_primes[i] == 0)
                    return false;

            while (r.IsEven)
            {
                s++;
                r >>= 1;
            }

            if (k < 1) k = 1;
            if (k > 54) k = 54;

            for (int round = 0; round < k; round++)
            {
                BigInteger x = BigInteger.ModPow(base_primes[round], r, n);
                for (int i = 0; i < s; i++)
                {
                    x = (x * x) % n;
                    if (x.IsOne)
                        break;
                }
                if (!x.IsOne && x != n - 1)
                    return false;
            }
            return true;
        }

        public void PrimeTriplet_Test()
        {
            for (BigInteger X = PrimeTriplet(4); ; X += 2)
                if (MillerRabin(X, 2) && MillerRabin(X + 6, 2))
                    if (MillerRabin(X + 2, 2))
                        WriteLine("{0}\n{1}\n{2}\n", X.ToString(), (X + 2).ToString(), (X + 6).ToString());
                    else
                        if (MillerRabin(X + 4, 2))
                            WriteLine("{0}\n{1}\n{2}\n", X.ToString(), (X + 4).ToString(), (X + 6).ToString());
        }

        public void TwinPrime_Test()
        {
            for (BigInteger X = TwinPrime(12); ; X += 2)
                if (MillerRabin(X, 2) && MillerRabin(X + 2, 2))
                    WriteLine("{0}\n{1}\n", X.ToString(), (X + 2).ToString());
        }

        public void Mersenne(int n)
        {
            BigInteger Pow2Sub1, rem;
            string strPow2Sub1;

            //for (int i = 0, x = 2; i < primes.Length; i++)
            int x = 2;
            Parallel.For(0, primes.Length, (int i) =>
            {
                Pow2Sub1 = new BigInteger(1) << (int)primes[i];
                Pow2Sub1 -= 1;
                //sw1.Restart();
                rem = BigInteger.ModPow(3, Pow2Sub1 - 1, Pow2Sub1);
                if (rem.IsOne)
                {
                    //sw1.Stop();
                    strPow2Sub1 = Pow2Sub1.ToString();
                    if (x < 10)
                        WriteLine("M[{0}] = {1}", primes[i], strPow2Sub1);
                    else
                        WriteLine("M[{0}] = {1}...{2}", primes[i], strPow2Sub1.Substring(0, 12), strPow2Sub1.Substring(strPow2Sub1.Length - 12, 12));
                    x++;
                    //WriteLine("elapsed time: {0} ms\n", sw1.ElapsedMilliseconds);
                }
            });
        }

        bool LucasLehmer(int n)
        {
            BigInteger seed = 4;
            BigInteger div = (new BigInteger(1) << n) - 1;      // div = 2^n - 1

            for (BigInteger i = 3; i <= n; i++)
            {
                seed = (seed * seed - 2) % div;
            }
            return (seed == 0);
        }

        // Use LucasLehmer to determine if 2^n-1 is prime
        public void Mersenne2(int n)
        {
            BigInteger Pow2Sub1;
            bool isMprime;
            string strPow2Sub1;

            sw1.Start();
            for (int i = 0, x = 1; i < primes.Length; i++)
            {
                isMprime = LucasLehmer((int)primes[i]);

                if (isMprime)
                {
                    sw1.Stop();
                    Pow2Sub1 = BigInteger.Pow(2, (int)primes[i]) - 1;
                    strPow2Sub1 = Pow2Sub1.ToString();
                    if (x < 10)
                        WriteLine("M[{0}] = {1}", primes[i], strPow2Sub1);
                    else
                        WriteLine("M[{0}] = {1}...{2}", primes[i], strPow2Sub1.Substring(0, 12), strPow2Sub1.Substring(strPow2Sub1.Length - 12, 12));
                    x++;
                    WriteLine("elapsed time: {0} ms\n", sw1.ElapsedMilliseconds);
                    sw1.Restart();
                }
                if (n < x)
                    break;
            }
        }

        public void RSA_Numbers()
        {
            BigInteger P = RandPrime(10);
            BigInteger Q = PrimeTriplet(10);
            BigInteger N = P * Q;
            BigInteger e = new BigInteger(65537);
            BigInteger phiN = (P - 1) * (Q - 1);
            //WriteLine("GCD({0}, \n    {1}) = {2}\n", phiN.ToString(), N, BigInteger.GreatestCommonDivisor(phiN, N));

            BigInteger d = InverseMod(e, phiN);

            WriteLine("RSA_Numbers()\n");
            WriteLine("P = {0}", P.ToString());
            WriteLine("Q = {0}", Q.ToString());
            WriteLine("N = {0}", N.ToString());
            WriteLine("e = {0}", e.ToString());
            WriteLine("d = {0}", d.ToString());

            BigInteger enc = BigInteger.ModPow(3126225153, e, N);

            BigInteger dP = d % (P - 1);
            BigInteger dQ = d % (Q - 1);
            BigInteger invQ = InverseMod(Q, P);
            // Chinese remainder
            BigInteger m1 = BigInteger.ModPow(enc, dP, P);
            BigInteger m2 = BigInteger.ModPow(enc, dQ, Q);
            BigInteger h = invQ * (m1 - m2);
            if (h.Sign < 0)
                h = -h;
            h %= P;
            //BigInteger dec = m2 + h * Q;

            BigInteger dec = BigInteger.ModPow(enc, d, N);
            WriteLine("enc = {0}", enc.ToString());
            WriteLine("dec = {0}\n", dec.ToString());
        }

        public void ModPow_Misc_Stuff()
        {
            BigInteger N = RandPrime(7);
            double Temp = BigInteger.Log10(N);
            int nbrPrimes = (int)Math.Exp(Math.Sqrt(Temp * Math.Log(Temp)) * 0.318);
            BigInteger T1 = BigInteger.Pow(new BigInteger(2), 1048576);         // 315653 digit number!
            T1 = (new BigInteger(1) << 9689) - 1;
            double LogT1 = BigInteger.Log10(T1);

            //StreamWriter file1 = new StreamWriter("output.txt", false);
            //file1.WriteLine(T1.ToString());
            //file1.Close();

            sw1.Restart();
            BigInteger T2 = BigInteger.ModPow(new BigInteger(13), T1 - 1, T1);
            sw1.Stop();
            WriteLine("ModPow time: {0} ms\n", sw1.ElapsedMilliseconds);                // ModPow time: 12453 ms
            double LogT2 = BigInteger.Log10(T2);

            //WriteLine("sqrt(2) = {0}\n", c.SquareRoot(BigInteger.Parse("2" + new String('0', 10000))));
            int n = 13017;  //7921;   // 1789;   // 3607;
            //WriteLine("fact({1}) = {0}\n", c.Factorial(n).ToString(), n);
            //WriteLine("fibonacci({1}) = {0}\n", c.Fibonacci(n).ToString(), n);

        }

        BigInteger g (BigInteger x, BigInteger n, int a) 
        {
            BigInteger x_ = x * x + a;
	        return BigInteger.Remainder(x_, n);
        }

        Int64 gx (Int64 x, Int64 n, Int64 a)
        {
            return (x * x + a) % n;
        }

        BigInteger Pollard_Rho(BigInteger n, int a)
        {
	        BigInteger x_fixed = 2;
	        int cycle_size = 2, count = 1;
	        BigInteger x = 2;
	        BigInteger h = 1;
            BigInteger x_;
 
	        while (h == 1) {
		        count = 1;
 
		        while (count <= cycle_size && h == 1) {
                    //x = g(x, n, a);
                    x_ = x * x + a;
                    x = BigInteger.Remainder(x_, n);
			        //x = gx(Int64.Parse(x.ToString()), Int64.Parse(n.ToString()), a);
                    //WriteLine("x = {0}", (x-x_fixed).ToString());
			        count++;
			        h = BigInteger.GreatestCommonDivisor(x - x_fixed, n);
                    //WriteLine("h = {0}", h.ToString());
		        }
 
		        if (h != 1)
			        break;
 
		        cycle_size *= 2;
                WriteLine("cycle_size = {0,-8}\tx = {1}", cycle_size, x);
		        x_fixed = x;
	        }
            WriteLine("count = {0}\n", count);
        	return h;
        }

        public void Pollard_Rho_Test()
        {
            BigInteger N1;
            // msieve factorized this 250-bit number in ~3mins.
            //N1 = BigInteger.Parse("923177721865685175285240199236472361656683591279028656230171797690188269779");

            N1 = BigInteger.Parse("20000000000000000672000000000000002907");
            //N1 = BigInteger.Parse("1152656570285234495703667671274025629");     // Time: 2358867 ms     Time: 1873793 ms        
                                                                                // (Time: 502594 ms    Time: 430157 ms - command-line Debug\RSABigInt.exe)
            //N1 = BigInteger.Parse("43272494503935639032000984197");             // Time: 28926 ms - command-line
            //N1 = BigInteger.Parse("462717344089999398416479");                  // Time: 988 ms       (Time: 873 ms - command-line)
            //N1 = BigInteger.Parse("12923855417829126637");                    // 20-digits - i.e. GE than 64-bits.
            //N1 = BigInteger.Parse("3369738766071892021");
            //N1 = BigInteger.Parse("139078421707568423");
            //N1 = BigInteger.Parse("87256236345731407");
            //N1 = BigInteger.Parse("4607863703200169");
            //N1 = BigInteger.Parse("373463523233483");
            //N1 = BigInteger.Parse("135723676817");
            //N1 = new BigInteger(21530071);
            //N1 = new BigInteger(12546257);
            const int a = 1;

            WriteLine("Pollard_Rho_Test()");
            sw1.Restart();
            BigInteger P1 = Pollard_Rho(N1, a);
            sw1.Stop();
            
            BigInteger Q1 = N1 / P1;
            WriteLine("Pollard_Rho({0}, {3}) = {1} x {2}", N1, P1, Q1, a);
            WriteLine("Time: {0} ms\n", sw1.ElapsedMilliseconds);
        }

        public void Smooth_Nums_Test(string S1)
        {
            BigInteger N;
            //N = BigInteger.Parse("21818232425302600378616644247667406319");
            // 2495.8 s, 2620 primes
            // 7217.7 s, 2122 primes, 4244 smooth numbers

            // NB - 8 logical cores!
            //Factor base: 1732 primes.
            //Collected 1906 smooth numbers.
            //Elapsed time: 1002.0 s

            //Factor base: 2494 primes.
            //Collected 2744 smooth numbers.
            //Elapsed time: 1098.2 s

            //Factor base: 2494 primes.
            //Collected 2744 smooth numbers.
            //Elapsed time: 1015.9 s

            //Factor base: 2494 primes.
            //Collected 2744 smooth numbers.
            //Elapsed time: 2883.8 s


            //N = BigInteger.Parse("16780348553824466403143254714822486311526698791663230901013034295820739731481287491453090350078076622143");
            //             N = BigInteger.Parse("10218568504117913286880427471505442091");                 // is a prime number!
            // 7551.6 s, 6055 primes

            //N = BigInteger.Parse("1152656570285234495703667671274025629");
            // 2888.0 s, 1086 primes        2567.8 s, 1593 primes       2613.5 s, 1803 primes       2693.4 s, 2200 primes       3103.5 s, 6059 primes 
            // 2120.8 s, 1086 primes        2017.5 s, 2570 primes      (command-line: Debug\RSABigInt.exe)            
            //                                  2022.9 s, 2570 primes      (command-line: Debug\RSABigInt.exe)
            // Factor base: 3340 primes.
            // Collected 3674 smooth numbers.
            // Elapsed time: 2086.6 s

            //Factor base: 1986 primes.
            //Collected 2184 smooth numbers.
            //Elapsed time: 1972.6 s

            //Factor base: 1986 primes.
            //Collected 2184 smooth numbers.
            //Elapsed time: 1768.9 s


            // 1898.6 s, 2923 primes, 3215 smooth numbers.
            // 5355.5 s, 2099 primes, 4198 smooth numbers          (command-line: Debug\RSABigInt.exe)
            // 5531.2 s, 1086 primes, 2172 smooth numbers.         (command-line: Debug\RSABigInt.exe)
            // 5818.4 s, 947 primes, 1894 smooth numbers.          (command-line: Debug\RSABigInt.exe)


            N = BigInteger.Parse("78029259347625822354842824158838188449");
            //Factor base: 3804 primes.
            //Collected 4184 smooth numbers.
            //Elapsed time: 10628.0 s

            // NB - 8 logical cores!
            //Factor base: 3804 primes.
            //Collected 4184 smooth numbers.
            //Elapsed time: 4142.7 s


            //N = BigInteger.Parse("3851667332709411289323864692105059");                 
            // 1528.2 s, 1801 primes         1617.0 s, 1018 primes        1409.1 s, 1018 primes
            //N = BigInteger.Parse("3851667332709411289323864692105059");
            // 881.1 s, 1801 primes          1006.7 s, 1018 primes        1021.0 s, 1018 primes                                                                                     
            // 3054.2 s, 4782 primes, 9564 smooth numbers.
            // 4221.6 s, 1018 primes, 2036 smooth numbers.
            // 4461.3 s, 1018 primes, 2036 smooth numbers.
            // 6893.3 s, 597 primes, 1194 smooth numbers.
            // 3149.7 s, 899 primes, 1798 smooth numbers.


            //N = BigInteger.Parse("43272494503935639032000984197");
            // SmoothNumbers
            // 2315.5 s, 286 primes, 572 smooth numbers.
            // 163.0 s,   610 primes
            // 232.2 s,  642 primes, 706 smooth numbers.
            // 149.5 s,  715 primes
            // 165.3 s, 740 primes
            // 394.2 s, 4814 primes
            // 601.8 s, 6075 primes

            // SmoothNumbers2
            // 115.3 s,  610 primes
            // 111.0 s, 715 primes
            // 109.9 s, 740 primes
            // 254.0 s, 4814 primes

            //Smooth_Numbers("990632981767960443643259");                           // 20.0 s,   154 primes         10.5 s, 596 primes           16.4 s, 1117 primes 
            //N = BigInteger.Parse("990632981767960443643259");                           //                             9.9 s, 596 primes          14.8 s, 1117 primes

            //N = BigInteger.Parse("462717344089999398416479");                           // 5.9 s,    269 primes
            // 34.1 s, 126 primes, 252 smooth numbers
            // 165.5 s, 126 primes, 252 smooth numbers


            //N = BigInteger.Parse("151770348516865739");
            //N = BigInteger.Parse("3369738766071892021");
            //N = BigInteger.Parse("802846957519667581");
            //N = BigInteger.Parse("12546257");
            // this one will take HOURS!

            //N = BigInteger.Parse("2017075389938133575596113187311764342781574681");
            // ECM.html: 26 s
            //2017075389938133575596113187311764342781574681 = 13976952717313892280427 x 144314388889610379224203


            // still takes HOURS!
            //N = BigInteger.Parse("4667112842259357358945637211043535865743957407");

            // Quicker...
            //N = BigInteger.Parse("492236049596491202533");

            // Factor base: 149 primes.
            // Collected 164 smooth numbers.
            // Elapsed time: 7.3 s
            //N = BigInteger.Parse("60052625181117476962049");

            // Factor base: 307 primes.
            // Collected 338 smooth numbers.
            // Elapsed time: 67.5 s
            //N = BigInteger.Parse("13591577121784133748648767");

            // Factor base: 424 primes.
            // Collected 466 smooth numbers.
            // Elapsed time: 20.5 s 
            //N = BigInteger.Parse("1024967568118884255087603281");


            // Factor base: 553 primes.
            // Collected 608 smooth numbers.
            //Elapsed time: 47.5 s

            // Factor base: 873 primes.
            // Collected 960 smooth numbers.
            // Elapsed time: 37.2 s
            //N = BigInteger.Parse("30054730572675466537888216717");

            // N = 2^2^7+1
            //N = BigInteger.Parse("340282366920938463463374607431768211457");


            double Temp = BigInteger.Log(N);
            uint sieve_max = (uint)Math.Exp(Math.Sqrt(Temp * Math.Log(Temp)) * 0.57);        // twiddle-factor
            prime_sieve(sieve_max);

            //uint SieveLimit = (uint)Math.Exp(8.5 + 0.015 * Temp);
            //uint SieveLimit = (uint)Math.Exp(Temp / 7.12);
            //prime_sieve(SieveLimit);

            //Smooth_Numbers(N);
            Smooth_Numbers2(N);

            Write("Press Enter: ");
            Console.ReadLine();

            Process_Matrix();
            //Dump_Matrix();
            Gauss_Elimination();
            //Dump_Matrix();
            //Calculate_Factors(N);
            Calculate_Factors_Task(N);
        }

        void Process_Matrix()
        {
            matrix = new uint[factor_base.Length*2, factor_base.Length*3];

            for (uint i = 0; i < Qx.Length; i++)
            {
                for (uint j = 0; j < Qx[i].exponents.Length; j++)
                    matrix[i, j] = Qx[i].exponents[j] & 1;          // Transpose values as well: rows become the prime exponents mod 2
                matrix[i, Qx[i].exponents.Length + i] = 1;          // set identity column value = 1
            }
        }

        void Gauss_Elimination()
        {
            uint row_adds = 0, row_swaps = 0;

            sw1.Restart(); 
            for (uint p = 0; p < matrix.GetLength(0); p++)                  // number of rows
            {
                // find pivot row and swap 
                for (uint i = p + 1; i < matrix.GetLength(0); i++)          // 
                {
                    if (matrix[i, p] > matrix[p, p])
                    {
                        //WriteLine("Swap rows: {0} and {1}", p, i);
                        row_swaps++;
                        for (uint j = 0; j < matrix.GetLength(1); j++)       // length of the 2nd dimension / number of columns
                        {
                            uint t = matrix[i, j];
                            matrix[i, j] = matrix[p, j];
                            matrix[p, j] = t;
                        }
                    }

                    if (matrix[i, p] == 1)                                  // Add these rows if value in pivot column is 1
                    {
                        //WriteLine("Add row: {0} to row: {1}", p, i);
                        row_adds++;
                        for (int j = 0; j < matrix.GetLength(1); j++)
                        {
                            matrix[i, j] ^= matrix[p, j];
                        }
                    }
                } // for i
            } // for p
            sw1.Stop();
            string strElapsed;
            if (sw1.ElapsedMilliseconds <= 1000)
                strElapsed = String.Format("{0} ms", sw1.ElapsedMilliseconds);
            else
                strElapsed = String.Format("{0:F1} s", (float)sw1.ElapsedMilliseconds / 1000);

            WriteLine("Row adds: {0}\nRow swaps: {1}\nElapsed time: {2}\n", row_adds, row_swaps, strElapsed);
        }

        void Dump_Matrix()
        {
            for (uint i = 0; i < matrix.GetLength(0); i++)                  // number of rows
            {
                Write("{0,3}: ", i);
                for (uint j = 0; j < matrix.GetLength(1); j++)              // number of columns
                    Write("{0} ", matrix[i, j]);
                WriteLine();
            }
        }
        ParallelLoopResult function()
        {
            ParallelLoopResult para_res = new ParallelLoopResult();
            return para_res;
        }

        void Calculate_Factors(BigInteger N1)
        {
            //for (uint i = (uint)matrix.GetLength(0) - 1; i >= 0; i--)                  // number of rows
            CancellationTokenSource cancellationSource = new CancellationTokenSource();
            ParallelOptions options = new ParallelOptions();

            options.CancellationToken = cancellationSource.Token;
            ParallelLoopResult res = Parallel.For(0, matrix.GetLength(0) - 1, options, (i, loopState) =>
            //ParallelAlgorithms.SpeculativeFor(0, matrix.GetLength(0) - 1, options, (i, loopState) =>
            {
                bool bNonNullFound = false;
                for (uint j = 0; j < factor_base.Length; j++)
                    if (matrix[i, j] != 0)                                             // test for null vector
                    {
                        bNonNullFound = true;
                        break;
                        //loopState.Stop();
                    }
                if (!bNonNullFound)                                                     
                {
                    // calculate smooth number from exponents, should be a perfect square
                    BigInteger x = 1, y = 1;
                    for (int j = factor_base.Length; j < matrix.GetLength(1); j++)
                        if (matrix[i, j] == 1)
                        {
                            x *= Qx[j - factor_base.Length].x;
                            y *= Qx[j - factor_base.Length].Q_of_x;
                        }
                    y = x - SquareRoot(y);
                    BigInteger P = BigInteger.GreatestCommonDivisor(N1, y);
                    if (P != 1 && P != N1)
                    {
                        BigInteger Q = N1 / P;
                        WriteLine("\nFactors: {0}, {1}\n", P.ToString(), Q.ToString());
                        loopState.Stop();
                        //return;
                    }
                }

            });
        }

        void Calculate_Factors_Task(BigInteger N1)
        {
            //for (uint i = (uint)matrix.GetLength(0) - 1; i >= 0; i--)                  // number of rows
            CancellationTokenSource cancellationSource = new CancellationTokenSource();
            Task[] sqrtTasks = new Task[matrix.GetLength(0)];
            
            for (int n = matrix.GetLength(0); n > 0; n--)
            {
                int i = n - 1;
                sqrtTasks[i] = Task.Factory.StartNew(() =>
                {
                    bool bNonNullFound = false;
                    for (uint j = 0; j < factor_base.Length; j++)
                        if (matrix[i, j] != 0)                                             // test for null vector
                        {
                            bNonNullFound = true;
                            break;
                        }
                    if (!bNonNullFound)
                    {
                        WriteLine("\nFound null vector matrix row[{0}]", i);
                        // calculate smooth number from exponents, should be a perfect square
                        BigInteger x = 1, y = 1;
                        for (int j = factor_base.Length; j < matrix.GetLength(1); j++)
                            if (matrix[i, j] == 1)
                            {
                                x *= Qx[j - factor_base.Length].x;
                                y *= Qx[j - factor_base.Length].Q_of_x;
                            }
                        y = x - SquareRoot(y);
                        BigInteger P = BigInteger.GreatestCommonDivisor(N1, y);
                        if (P != 1 && P != N1)
                        {
                            BigInteger Q = N1 / P;
                            WriteLine("\nThread ID #{0}\nFactors: {1}, {2}\n", Task.CurrentId, P.ToString(), Q.ToString());
                            cancellationSource.Cancel();
                            //return;
                        }
                    }
                }, cancellationSource.Token);
            }
            try
            {
                Task.WaitAll(sqrtTasks, cancellationSource.Token);
            }
            catch (OperationCanceledException ex)
            {
                WriteLine("\nOperation cancelled, done.");
            }
            finally
            {
                //cancellationSource.Dispose();
            }
        }
    }   // class MyBigInteger_Class

    class Program
    {
        static void Main(string[] args)
        {
            MyBigInteger_Class c = new MyBigInteger_Class();

            Assembly assem = typeof(BigInteger).Assembly;
            BigInteger p = (BigInteger)assem.CreateInstance("System.Numerics.BigInteger");

            //c.TwinPrime_Test();
            //c.PrimeTriplet_Test();
            //c.Mersenne2(23);
            c.Smooth_Nums_Test("");
            //c.RSA_Numbers();
            //c.ModPow_Misc_Stuff();
            //c.Pollard_Rho_Test();

            Write("\nPress Enter: ");
            Console.ReadLine();
        }
    }   // class
}   // namespace
