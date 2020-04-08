//#define _DEBUG
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Numerics;
using System.Reflection;
using System.Threading;
using System.Threading.Tasks;
using System.Threading.Algorithms;

using static System.Console;

#pragma warning disable IDE0055,IDE1006,IDE1005,IDE1017,CS0219,CS0168
/*
 * IDE1006 Suppress Naming Rule Violation IDE1006
 * IDE1005 Delegate invocation can be simplified
 * IDE1017 Object initialization can be simplified
 * CS0168  The variable 'var' is declared but never used.
 * CS0219  The variable 'variable' is assigned but its value is never used
 */

namespace RSABigInt
{
    class MyBigInteger_Class
    {
        //private const uint ARRAY_SIZE = 0x166e0e21;
        private const uint ARRAY_SIZE = 0x10000000;
        private const uint LIMIT = 10000000;
        private Random _randObj;
        private uint[] primes;               
        private uint[] factor_base;          //
        private uint[,] matrix;              // 2-dimensional matrix

        private struct smooth_num
        {
            public BigInteger Q_of_x;
            public BigInteger x;
            public uint[] exponents;
        };
        private smooth_num[] Qx;

        // constructor
        public MyBigInteger_Class()
        {
            _randObj = new Random((int)DateTime.Now.Ticks);
            primes = new uint[ARRAY_SIZE];                  // 131072 elements --- 0x18000000 = 1.5GB array
            factor_base = new uint[ARRAY_SIZE];
            prime_sieve(LIMIT);
        }

        public void prime_sieve(ulong n)
        {
            int p;
            primes.Initialize();

            Stopwatch sw = new Stopwatch();
            sw.Start();

            primes[0] = 2;
            for (p = 0; primes[p] <= n;) 
            {
                for (ulong i = primes[p]*primes[p]; i <= n; i+=primes[p])
                    primes[i] = 1;
                primes[++p] = primes[p-1] + 1;
                for (; primes[p] <= n && primes[primes[p]] == 1; primes[p]++) ; //find next prime (where s[p]==0)
            }
            Array.Resize(ref primes, p);

            sw.Stop();
#if DEBUG
            WriteLine("prime_sieve time took: {0}\n", FormatTimeSpan(sw.Elapsed));
#endif
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

        public BigInteger RandPrime(int size)
        {
            BigInteger rnd = BigInteger.Zero;
            BigInteger rem = BigInteger.Zero;
            BigInteger a = new BigInteger(2);
            Stopwatch sw = new Stopwatch();

            sw.Start();
            rnd = BigInteger.Zero;
            for (int i = 0; i < size; i++)
            {
                rnd <<= 16;
                rnd += _randObj.Next();
            }
            rnd |= 1;
            rem = BigInteger.ModPow(a, rnd - 1, rnd);

            while (!rem.IsOne)
            {
                rnd += 2;
                rem = BigInteger.ModPow(a, rnd - 1, rnd);
            }
            sw.Stop();
#if DEBUG
            WriteLine("RandPrime({0})\nElapsed time: {1}\n", size, FormatTimeSpan(sw.Elapsed));
#endif
            return rnd;
        }

        public BigInteger TwinPrime(int size)
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

        public BigInteger PrimeTriplet(int size)
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
            BigInteger d = n >> 1, q, _d;
            Stopwatch sw = new Stopwatch();

            sw.Start();
            //Newton's Method
            do
            {
                q = n / d + d;
                _d = d;
                q >>= 1;
                d = q;
            } while (_d > q);

            sw.Stop();

#if DEBUG
            WriteLine("\nSquareRoot({0})\nElapsed time: {1}\n", n, FormatTimeSpan(sw.Elapsed));
#endif

            return q;
        }

        // Why is this function 3 times(!) quicker than the one above?  Number of operations used.
        public BigInteger Sqrt(BigInteger x)
        {
            BigInteger div = BigInteger.One;
            div = BigInteger.Add(div, BigInteger.One);
            BigInteger TWO = new BigInteger(2);
            BigInteger div2 = div, y;
            Stopwatch sw = new Stopwatch();

            // Loop until we hit the same value twice in a row, or wind
            // up alternating.
            sw.Start();
            while (true)
            {
                y = BigInteger.Add(div, BigInteger.Divide(x, div));
                y >>= 1;
                if (y.Equals(div) || y.Equals(div2))
                    break;
                div2 = div;
                div = y;
            }
            sw.Stop();
#if DEBUG
            WriteLine("\nSquareRoot({0})\nElapsed time: {1}\n", x, FormatTimeSpan(sw.Elapsed));
#endif
            return y;
        }

        public BigInteger Factorial(int n)
        {
            BigInteger fact = BigInteger.One;
            Stopwatch sw = new Stopwatch();

            sw.Start();
            for (int i = 2; i <= n; i++)
                fact *= i;

            sw.Stop();
#if DEBUG
            WriteLine("\nFactorial({0}) Elapsed time: {1}\n", n, FormatTimeSpan(sw.Elapsed));
#endif
            return fact;
        }

        public BigInteger Fibonacci(int n)
        {
            BigInteger Fn = BigInteger.Zero;
            BigInteger Fn_plus_one = BigInteger.One;
            Stopwatch sw = new Stopwatch();

            sw.Start();
            for (int i = 1; i < n; i++)
            {
                BigInteger fib_temp = Fn_plus_one;
                Fn_plus_one += Fn;
                Fn = fib_temp;
            }

            sw.Stop();
#if DEBUG
            WriteLine("\nFactorial({0}) Elapsed time: {1}\n", n, FormatTimeSpan(sw.Elapsed));
#endif
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
            WriteLine($"Factor base: {j} primes.\n");
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
            int[] base_primes = {
                  2,   3,   5,   7,  11,  13,  17,  19,
	             23,  29,  31,  37,  41,  43,  47,  53,
	             59,  61,  67,  71,  73,  79,  83,  89,
	             97, 101, 103, 107, 109, 113, 127, 131,
	            137, 139, 149, 151, 157, 163, 167, 173,
	            179, 181, 191, 193, 197, 199, 211, 223,
	            227, 229, 233, 239, 241, 251
            };
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
            for (BigInteger X = PrimeTriplet(10); ; X += 2)
                if (MillerRabin(X, 2) && MillerRabin(X + 6, 2))
                    if (MillerRabin(X + 2, 2))
                        WriteLine("{0}\n{1}\n{2}\n", X.ToString(), (X + 2).ToString(), (X + 6).ToString());
                    else
                        if (MillerRabin(X + 4, 2))
                            WriteLine("{0}\n{1}\n{2}\n", X.ToString(), (X + 4).ToString(), (X + 6).ToString());
        }

        public void print_time(TextWriter F)
        {
            DateTime dt = DateTime.Now;
            string str_dt = String.Format("[{0} {1}]", dt.ToLongDateString(), dt.ToLongTimeString());
            WriteLine("{0}", str_dt);
            F.WriteLine(str_dt);
        }

        public string ByteArrayStruct(byte[] byte_array)
        {
            Stack<byte> reversed_bytes = new Stack<byte>();
            // Output byte [] structure suitable for BigInteger.cs
            foreach (byte b in byte_array)
                reversed_bytes.Push(b);

            string str_bytes = "";
            foreach (byte b in reversed_bytes)
                str_bytes += String.Format($"(byte)0x{b:x2}, ");
            return str_bytes;
        }

        public string FormatTimeSpan(TimeSpan ts)
        {
            string strElapsed;
            if (ts.TotalMilliseconds < 1000.0d )
                strElapsed = String.Format("{0} ms", ts.Milliseconds);
            else
                strElapsed = String.Format("{0:F1} s", ts.TotalSeconds);
            
            return strElapsed;
        }

        public void TwinPrime_Test()
        {
            BigInteger P = RandPrime(2);

            try
            {
                FileStream F_TP = new FileStream(@".\twin_primes.txt", FileMode.Append);
                using (StreamWriter writer = new StreamWriter(F_TP))
                {
                    DateTime dt = DateTime.Now;
                    int f = 0;

                    //for (BigInteger X = P; DateTime.Now < dt.AddHours(4.0d); X += 2)
                    for (BigInteger X = P; DateTime.Now < dt.AddMinutes(5.0d); X += 2)
                    {
                        switch (f)
                        {
                            case 0:
                                Write("[|]\r");
                                break;
                            case 1:
                                Write("[/]\r");
                                break;
                            case 2:
                                Write("[-]\r");
                                break;
                            case 3:
                                Write("[\\]\r");
                                break;
                        }
                        f++; f %= 4;

                        if (MillerRabin(X, 3) && MillerRabin(X + 2, 3))
                        {
                            //WriteLine("[{0} {1}]", DateTime.Now.ToLongDateString(), DateTime.Now.ToLongTimeString());
                            print_time(writer);
                            WriteLine("{0}\n{1}\n", X.ToString(), (X + 2).ToString());

                            // output to file
                            writer.WriteLine(X.ToString());
                            writer.WriteLine((X + 2).ToString());
                            writer.WriteLine();
                            writer.FlushAsync();
                        }
                    }
                }

                F_TP.Close();
            }
            catch
            {
                WriteLine("File opening failed.\n");
                return;
            }
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
                //sw.Restart();
                rem = BigInteger.ModPow(3, Pow2Sub1 - 1, Pow2Sub1);
                if (rem.IsOne)
                {
                    //sw.Stop();
                    strPow2Sub1 = Pow2Sub1.ToString();
                    if (x < 10)
                        WriteLine("M[{0}] = {1}", primes[i], strPow2Sub1);
                    else
                        WriteLine("M[{0}] = {1}...{2}", primes[i], strPow2Sub1.Substring(0, 12), strPow2Sub1.Substring(strPow2Sub1.Length - 12, 12));
                    x++;
                    //WriteLine("elapsed time: {0} ms\n", sw.ElapsedMilliseconds);
                }
            });
        }

        bool LucasLehmer(int n)
        {
            BigInteger seed = 4;
            //BigInteger seed= (new BigInteger(1) << n + 1) / 3;     // seed = (2^n + 1) / 3
            BigInteger div = (new BigInteger(1) << n) - 1;          // div = 2^n - 1

            for (BigInteger i = 3; i <= n; i++)
            {
                seed = (seed * seed - 2) % div;
            }
            return (seed == 0);
        }

        // Use LucasLehmer to determine if 2^n-1 is prime
        public void Mersenne2(int n)
        {
            BigInteger PowerOf2Sub1;
            bool isMprime;
            string strPowerOf2Sub1;
            Stopwatch sw = new Stopwatch();

            sw.Start();
            for (int i = 0, numberOfMprimes = 1; i < primes.Length; i++)
            {
                isMprime = LucasLehmer((int)primes[i]);

                if (isMprime)
                {
                    sw.Stop();
                    PowerOf2Sub1 = BigInteger.Pow(2, (int)primes[i]) - 1;
                    strPowerOf2Sub1 = PowerOf2Sub1.ToString();

                    if (numberOfMprimes < 9)
                        WriteLine("M[{0}] = {1}", primes[i], strPowerOf2Sub1);
                    else
                        WriteLine("M[{0}] = {1}...{2}", primes[i], strPowerOf2Sub1.Substring(0, 12), 
                                                                   strPowerOf2Sub1.Substring(strPowerOf2Sub1.Length - 12, 12));

                    numberOfMprimes++;

                    WriteLine("elapsed time: {0} ms\n", sw.ElapsedMilliseconds);
                    sw.Restart();
                }
                if (n < numberOfMprimes)
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
            var N = RandPrime(29);
            double Temp = BigInteger.Log10(N);
            int nbrPrimes = (int)Math.Exp(Math.Sqrt(Temp * Math.Log(Temp)) * 0.618);

            WriteLine( ByteArrayStruct(N.ToByteArray()) );

            var T1 = BigInteger.Pow(new BigInteger(2), 1048576);                        // 315653 digit number!
            var T2 = (new BigInteger(1) << 9689) - 1;
            double LogT1 = BigInteger.Log10(T1);
            var P1 = BigInteger.Parse("8949969815784082905285113653565030657117978813653332368993611264200624281180341263589905784897611545421273844719391941113720317582959695290277880367278839");

            bool bIsPrime = MillerRabin(P1, 13);
            WriteLine($"MillerRabin({P1}, 13): {bIsPrime}\n");

            var P2 = new BigInteger(new byte[] { 
                (byte)0x95, (byte)0xe3, (byte)0x5d, (byte)0x14, (byte)0xe5, (byte)0x30, 
                (byte)0x1e, (byte)0xbd, (byte)0x76, (byte)0x92, (byte)0xa1, (byte)0x26, 
                (byte)0xe7, (byte)0xfa, (byte)0xe2, (byte)0xef, (byte)0xfd, (byte)0x22, 
                (byte)0xea, (byte)0xb7, (byte)0x1b, (byte)0x7e, (byte)0xd2, (byte)0x8d, 
                (byte)0x95, (byte)0x38, (byte)0x46, (byte)0xb7, (byte)0x67, (byte)0xc2, 
                (byte)0xbb, (byte)0xff, (byte)0x3a, (byte)0x0f, (byte)0xf9, (byte)0x4e, 
                (byte)0x71, (byte)0xcb, (byte)0x4c, (byte)0xe1, (byte)0x23, (byte)0xff, 
                (byte)0xab, (byte)0xdf, (byte)0x4f, (byte)0x05, (byte)0x4d, (byte)0x86, 
                (byte)0xa8, (byte)0xd5, (byte)0x0e, (byte)0x0a, (byte)0x81, (byte)0xae, 
                (byte)0x16, (byte)0x84, (byte)0xb5, (byte)0x08, (byte)0x6b, (byte)0xef, 
                (byte)0x68, (byte)0x30, (byte)0x01, (byte)0xe7,
                (byte)0x00
            });

            bIsPrime = MillerRabin(P2, 13);
            WriteLine($"MillerRabin({P2}, 13): {bIsPrime}\n");

            var P3 = new BigInteger(new byte[] {
                (byte)0x81, (byte)0x3f, (byte)0x9c, (byte)0x81, (byte)0x31, (byte)0x78,
                (byte)0x58, (byte)0xa1, (byte)0xcd, (byte)0xbd, (byte)0xdd, (byte)0xdb,
                (byte)0xc9, (byte)0xa7, (byte)0xb1, (byte)0xcf, (byte)0x53, (byte)0x92,
                (byte)0x26, (byte)0x80, (byte)0x53, (byte)0x89, (byte)0xe5, (byte)0x80,
                (byte)0x26, (byte)0x60, (byte)0x23, (byte)0x6a, (byte)0x79, (byte)0xc8,
                (byte)0x1f, (byte)0xf6, (byte)0xb2, (byte)0x63, (byte)0x87, (byte)0x2e,
                (byte)0x74, (byte)0xe2, (byte)0x6c, (byte)0x0b, (byte)0xfb, (byte)0x2e,
                (byte)0xb6, (byte)0xe6, (byte)0xa0, (byte)0x02, (byte)0xb1, (byte)0x69,
                (byte)0x71, (byte)0xc7, (byte)0x47, (byte)0xe9, (byte)0x44, (byte)0x9d,
                (byte)0x43, (byte)0x1a, (byte)0x86, (byte)0x39, (byte)0xf5, (byte)0x2a,
                (byte)0x9b, (byte)0xe8, (byte)0x07, (byte)0xda,
                (byte)0x00
                /*
                (byte)0xc5, (byte)0x74, (byte)0x8c, (byte)0xd5, (byte)0x3d, (byte)0xd3,
                (byte)0x52, (byte)0x40, (byte)0x06, (byte)0x69, (byte)0xbb, (byte)0x82,
                (byte)0xe2, (byte)0x21, (byte)0x66, (byte)0x63, (byte)0xd8, (byte)0xef,
                (byte)0xf2, (byte)0xe3, (byte)0x28, (byte)0x3f, (byte)0x1a, (byte)0xd8,
                (byte)0xf1, (byte)0x07, (byte)0xad, (byte)0x9f, (byte)0xea, (byte)0x8e,
                (byte)0xb8, (byte)0x39, (byte)0x2a, (byte)0x94, (byte)0x42, (byte)0xda,
                (byte)0x0c, (byte)0xb9, (byte)0x63, (byte)0xe4, (byte)0xe2, (byte)0x8b,
                (byte)0x9c, (byte)0x15, (byte)0x08, (byte)0x12, (byte)0x7c, (byte)0xde,
                (byte)0xc8, (byte)0x6c, (byte)0x30, (byte)0xe9, (byte)0x5f, (byte)0x9e,
                (byte)0xc1, (byte)0xbe, (byte)0x92, (byte)0x34, (byte)0xf8, (byte)0xaf,
                (byte)0x7a, (byte)0x23, (byte)0xfd, (byte)0x93,
                (byte)0x00*/
            });

            P3 = new BigInteger(new byte[] {
                (byte)0x37, (byte)0x61, (byte)0x8c, (byte)0x03, (byte)0x96, (byte)0xed,
                (byte)0x2d, (byte)0x2b, (byte)0x59, (byte)0x09, (byte)0xea, (byte)0xa7,
                (byte)0xfd, (byte)0x91, (byte)0x95, (byte)0x90, (byte)0x57, (byte)0x34,
                (byte)0x73, (byte)0x82, (byte)0x31, (byte)0x31, (byte)0x06, (byte)0x8b,
                (byte)0xa4, (byte)0x03, (byte)0xe7, (byte)0x3b, (byte)0x58, (byte)0x10,
                (byte)0xf4, (byte)0x08, (byte)0xe9, (byte)0x3c, (byte)0x4b, (byte)0x8f,
                (byte)0x2e, (byte)0xf3, (byte)0xfa, (byte)0x7f, (byte)0x11, (byte)0x90,
                (byte)0xd6, (byte)0xd2, (byte)0x40, (byte)0xc3, (byte)0xa2, (byte)0x45,
                (byte)0x8d, (byte)0xa1, (byte)0x56, (byte)0x98, (byte)0x6b, (byte)0x7a,
                (byte)0x04, (byte)0x81, (byte)0xd3, (byte)0x50, (byte)0x39, (byte)0xe7,
                (byte)0x32, (byte)0xfe, (byte)0x01, (byte)0xf3,
                (byte)0x00
            });

            P3 = new BigInteger(new byte[]
            {
                (byte)0x9d, (byte)0x4e, (byte)0x78, (byte)0x54, (byte)0x43, (byte)0x1e,
                (byte)0x1f, (byte)0xc8, (byte)0x71, (byte)0x42, (byte)0x71, (byte)0xbe,
                (byte)0xc3, (byte)0x26, (byte)0x9e, (byte)0xbe, (byte)0xf4, (byte)0x0b,
                (byte)0x15, (byte)0x5c, (byte)0x52, (byte)0x5a, (byte)0x80, (byte)0x00,
                (byte)0x7a, (byte)0x80, (byte)0x56, (byte)0x33, (byte)0xe8, (byte)0x42,
                (byte)0x22, (byte)0x3e, (byte)0x50, (byte)0x2f, (byte)0xf7, (byte)0x6a,
                (byte)0xf7, (byte)0x85, (byte)0x13, (byte)0xff, (byte)0xd5, (byte)0x93,
                (byte)0xfd, (byte)0x8b, (byte)0x44, (byte)0xc5, (byte)0xf4, (byte)0x10,
                (byte)0x97, (byte)0x04, (byte)0x5e, (byte)0xd4, (byte)0x17, (byte)0x85,
                (byte)0x47, (byte)0xc2, (byte)0xd5, (byte)0xc1, (byte)0xe0, (byte)0xaf,
                (byte)0x0e, (byte)0x4f, (byte)0x8a, (byte)0x9e,
                (byte)0x00
            });
            bIsPrime = MillerRabin(P3, 13);
            WriteLine($"MillerRabin({P3}, 13): {bIsPrime}\n");

            //StreamWriter file1 = new StreamWriter("output.txt", false);
            //file1.WriteLine(T1.ToString());
            //file1.Close();

            Stopwatch sw = new Stopwatch();
            BigInteger T3;
            sw.Start();
            {
                T3 = BigInteger.ModPow(new BigInteger(31), T2, T2);
            }
            sw.Stop();

                                                                                        // This could take a few hours!
            WriteLine("ModPow time: {0}\n", FormatTimeSpan(sw.Elapsed));                 // ModPow time: 12453 ms

            sw.Restart();
            {
                double LogT3 = BigInteger.Log10(T3);
            }
            sw.Stop();
            WriteLine("Log10(T3) elapsed time: {0} ms\n", sw.ElapsedMilliseconds);                 // ModPow time: 12453 ms

            string strNormalizedIntegerTwo = "2" + new String('0', 10000);

            WriteLine(SquareRoot(BigInteger.Parse(strNormalizedIntegerTwo)) + "\n");
            WriteLine(Sqrt(BigInteger.Parse(strNormalizedIntegerTwo)) + "\n");
            
            //int n = 13017;  //7921;   // 1789;   // 3607;
            //WriteLine("fact({1}) = {0}\n", Factorial(n).ToString(), n);
            //WriteLine("fibonacci({1}) = {0}\n", Fibonacci(n).ToString(), n);
            //BigInteger sqrt2 = SquareRoot(BigInteger.Parse(strNormalizedIntegerTwo));
            //WriteLine($"sqrt(2) = {sqrt2}\n");

            int n = 13017;  //7921;   // 1789;   // 3607;
            WriteLine("fact({1}) = {0}\n", Factorial(n), n);
            WriteLine("fibonacci({1}) = {0}\n", Fibonacci(n), n);
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
            WriteLine($"count = {count}\n");

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
            Stopwatch sw = new Stopwatch();

            WriteLine("Pollard_Rho_Test()");
            sw.Start();
                BigInteger P1 = Pollard_Rho(N1, a);
            sw.Stop();
            
            BigInteger Q1 = N1 / P1;
            WriteLine("Pollard_Rho({0}, {3}) = {1} x {2}", N1, P1, Q1, a);
            WriteLine("Time: {0} ms\n", sw.ElapsedMilliseconds);
        }

        void Process_Matrix()
        {
            Stopwatch sw = new Stopwatch();
            sw.Start();

            matrix = new uint[factor_base.Length*2, factor_base.Length*3];
            // TO-DO: Parallelize the outer loop?
            for (uint i = 0; i < Qx.Length; i++)
            {
                for (uint j = 0; j < Qx[i].exponents.Length; j++)
                    matrix[i, j] = Qx[i].exponents[j] & 1;          // Transpose values as well: rows become the prime exponents mod 2
                matrix[i, Qx[i].exponents.Length + i] = 1;          // set identity column value = 1
            }

            sw.Stop();
#if DEBUG
            string strValue = $"Process_Matrix() Elapsed time: {FormatTimeSpan(sw.Elapsed)}\n";
            WriteLine(strValue);
#endif
        }

        void Gauss_Elimination()
        {
            uint row_adds = 0, row_swaps = 0;
            Stopwatch sw = new Stopwatch();
            CancellationTokenSource cancellationSource = new CancellationTokenSource();
            ParallelOptions parallelOptions = new ParallelOptions()
            {
                CancellationToken = cancellationSource.Token
            };

            // TO-DO: Parallelize the loops!
            //for (uint p = 0; p < matrix.GetLength(0); p++)                  // number of rows
            sw.Start();
            /*
             * DO NOT parallelize the outer for p loop - somehow breaks elimination process!
             */
            //ParallelLoopResult res = Parallel.For(0, matrix.GetLength(0), parallelOptions, (p, loopState) =>
            for (uint p = 0; p < matrix.GetLength(0); p++)                    // number of rows
            {
                // find pivot row and swap 
                for (long i = p + 1; i < matrix.GetLength(0); i++)              // 
                {
                    if (matrix[i, p] > matrix[p, p])
                    {
#if DEBUG
                        WriteLine("Swap rows: {0} and {1}", p, i);
#endif
                        row_swaps++;
                        for (uint j = 0; j < matrix.GetLength(1); j++)          // length of the 2nd dimension / number of columns
                        {
                            uint t = matrix[i, j];
                            matrix[i, j] = matrix[p, j];
                            matrix[p, j] = t;
                        }
                    }

                    if (matrix[i, p] == 1)                                  // Add these rows if value in pivot column is 1
                    {
#if DEBUG
                        WriteLine("Add row: {0} to row: {1}", p, i);
#endif
                        row_adds++;
                        for (int j = 0; j < matrix.GetLength(1); j++)
                        {
                            matrix[i, j] ^= matrix[p, j];
                        }
                    }
                } // for i
            }     // for p - NOT: Parallel.For p
            sw.Stop();
#if DEBUG
            string strValue = $"Row adds: {row_adds}\nRow swaps: {row_swaps}\nElapsed time: {FormatTimeSpan(sw.Elapsed)}\n";
            WriteLine(strValue);
#endif
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
            ParallelOptions parallelOptions = new ParallelOptions()
            {
                CancellationToken = cancellationSource.Token
            };

            Stopwatch sw = new Stopwatch();
            sw.Start();
            DateTime dt0 = DateTime.Now;

            //ParallelAlgorithms.SpeculativeFor(fromInclusive: 0, toExclusive: matrix.GetLength(0) - 1, options: parallelOptions, body: () => 
            try
            {
                ParallelLoopResult res = Parallel.For(0, matrix.GetLength(0) - 1, parallelOptions, (i, loopState) =>
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
                        y = x - Sqrt(y);
                        BigInteger P = BigInteger.GreatestCommonDivisor(N1, y);
                        if (P > 1 && P != N1)
                        {
                            BigInteger Q = N1 / P;
                            WriteLine("\nFactors: {0}, {1}\n", P.ToString(), Q.ToString());
                            loopState.Stop();
                            cancellationSource.Cancel();
                        }
                    }

                } );     // ParallelFor(...)
            }
            catch (OperationCanceledException ex)
            {
                WriteLine("Caught exception: {0}\n", ex.Message);
                WriteLine("\nOperation cancelled, done.");
            }
            finally
            {
                cancellationSource.Dispose();
            }

            DateTime dt1 = DateTime.Now;
            sw.Stop();
#if DEBUG
            WriteLine("Calculate_Factors({0})\nElapsed time: {1}", N1, FormatTimeSpan(sw.Elapsed));
            WriteLine($"dt1 - dt0 = {dt1.Subtract(dt0).Seconds} s\n");
#endif
        }   // CalculateFactors

        void Calculate_Factors_Task(BigInteger N1)
        {
            CancellationTokenSource cancellationSource = new CancellationTokenSource();
            Task[] sqrtTasks = new Task[matrix.GetLength(0)];
            Stopwatch sw = new Stopwatch();
            sw.Start();

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
#if DEBUG
                        WriteLine("\nFound null vector matrix row[{0}]", i);
#endif
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
                WriteLine("Caught exception: {0}\n", ex.Message);
                WriteLine("\nOperation cancelled, done.");
            }
            finally
            {
                cancellationSource.Dispose();
            }

            sw.Stop();
#if DEBUG
            WriteLine("Calculate_Factors_Task({0})\nElapsed time: {1}\n", N1, FormatTimeSpan(sw.Elapsed));
#endif
        }

        public void Smooth_Numbers(BigInteger N1)
        {
            BigInteger sqrt_N1 = SquareRoot(N1);
            BigInteger i = sqrt_N1 + 1;
            BigInteger j = sqrt_N1 - 1;

            // Collect smooth numbers
            Factor_Base(N1);

            uint N_smooths = (uint)(factor_base.Length * 1.01d);
            if ((N_smooths & 1) == 1)
                N_smooths++;                // make it even
            Qx = new smooth_num[N_smooths];
            Qx.Initialize();
            long k = -1;

            Stopwatch sw = new Stopwatch();
            sw.Start();

            Task[] smooth = new Task[2];
            smooth[0] = Task.Run(() =>
            {
                while (k < N_smooths - 1)
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
                while (k < N_smooths - 1)
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

            sw.Stop();
            string strElapsed;
            if (sw.ElapsedMilliseconds <= 1000)
                strElapsed = String.Format("{0} ms", sw.ElapsedMilliseconds);
            else
                strElapsed = String.Format("{0:F1} s", (float)sw.ElapsedMilliseconds / 1000);

            WriteLine("Collected {0} smooth numbers.\nElapsed time: {1}\n", k, strElapsed);
            //WriteLine("{0}\t{1}", i - sqrt_N1, sqrt_N1 - j);
        }

        public void Smooth_Numbers2(BigInteger N1)
        {
            BigInteger sqrt_N1 = Sqrt(N1);
            BigInteger i = sqrt_N1 + 1;
            BigInteger j = sqrt_N1 - 1;

            // prime number factors
            Factor_Base(N1);
            uint N_smooths = (uint)(factor_base.Length * 1.01d);
            if ((N_smooths & 1) == 1)
                N_smooths++;                // make it even
            Qx = new smooth_num[N_smooths];
            Qx.Initialize();

            smooth_num[] Q1x = new smooth_num[N_smooths];
            Q1x.Initialize();

            long k = 0;
            Stopwatch sw = new Stopwatch();
            sw.Start();

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
                ParallelOptions parallelOptions = new ParallelOptions()
                {
                    CancellationToken = cancellationSource.Token
                };
                Parallel.For(0, Q1x.Length, parallelOptions, (ii, loopState) =>
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
                    catch (IndexOutOfRangeException ex)
                    {
                        loopState.Stop();
                        WriteLine("Caught exception: " + ex.Message);
                    }
                }
                );
                Write("{0} smooth numbers\r", k);
            }   // while (k < factor_base.Length) 
            sw.Stop();
#if DEBUG
            WriteLine("Collected {0} smooth numbers.\nElapsed time: {1}\n", k, FormatTimeSpan(sw.Elapsed));
#endif
        }   // Smooth_Numbers2

        public void Smooth_Nums_Test(string S1)
        {
            BigInteger N = BigInteger.Parse(S1);
            #region _historical_timings
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


            //N = BigInteger.Parse("78029259347625822354842824158838188449");
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

            // "9251887165329150354056716315122396153271557067859755802728429989905317141127"
#endregion
            double Temp = BigInteger.Log(N);
            WriteLine("Log(N): {0:F12}", Temp);
            uint sieve_max = (uint)Math.Exp(Math.Sqrt(Temp * Math.Log(Temp)) * 0.54);        // twiddle-factor
            WriteLine("sieve_max: {0}", sieve_max);
            prime_sieve(sieve_max);

            //uint SieveLimit = (uint)Math.Exp(8.5 + 0.015 * Temp);
            //uint SieveLimit = (uint)Math.Exp(Temp / 7.12);
            //prime_sieve(SieveLimit);

            // original Smooth_Numbers only uses 2 threads (Tasks)!
            //Smooth_Numbers(N);
            // Parallel_For implementation
            Smooth_Numbers2(N);

            //Write("Press Enter: ");
            //Console.ReadLine();

            Process_Matrix();
            //Dump_Matrix();
            Gauss_Elimination();
            //Dump_Matrix();
            Calculate_Factors(N);
            //Calculate_Factors_Task(N);
        }

    /*
        public void Smooth_Numbers2(BigInteger N1)
        {
            BigInteger sqrt_N1 = SquareRoot(N1);
            BigInteger i = sqrt_N1 + 1;
            BigInteger j = sqrt_N1 - 1;

            // prime number factors
            Factor_Base(N1);
            uint N_smooths = (uint)(factor_base.Length * 1.01d);
            if ((N_smooths & 1) == 1)
                N_smooths++;                // make it even
            Qx = new smooth_num[N_smooths];
            Qx.Initialize();

            smooth_num[] Q1x = new smooth_num[N_smooths];
            Q1x.Initialize();

            long k = 0;
            Stopwatch sw = new Stopwatch();
            sw.Start();

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
                ParallelOptions parallelOptions = new ParallelOptions()
                {
                    CancellationToken = cancellationSource.Token
                };
                Parallel.For(0, Q1x.Length, parallelOptions, (ii, loopState) =>
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
                    catch (IndexOutOfRangeException ex)
                    {
                        loopState.Stop();
                        WriteLine("Caught exception: " + ex.Message);
                    }
                }
                );
                Write("{0} smooth numbers\r", k);
            }   // while (k < factor_base.Length) 

            sw.Stop();
#if DEBUG
            string strElapsed;
            if (sw.ElapsedMilliseconds <= 1000)
                strElapsed = String.Format("{0} ms", sw.ElapsedMilliseconds);
            else
                strElapsed = String.Format("{0:F1} s", (float)sw.Elapsed.Seconds);

            WriteLine("Collected {k} smooth numbers.\nElapsed time: {strElapsed}\n");
#endif
        }   // Smooth_Numbers2
    */
    }   // class MyBigInteger_Class

    class Program
    {
        static void Main(string[] args)
        {
            MyBigInteger_Class clsMBI = new MyBigInteger_Class();

            //Assembly assem = typeof(BigInteger).Assembly;
            //BigInteger p = (BigInteger)assem.CreateInstance("System.Numerics.BigInteger");

            BigInteger p = clsMBI.RandPrime(3);
            BigInteger q = clsMBI.RandPrime(3);
            BigInteger N = p * q;

            WriteLine($"{p} x {q} = {N}\n");

            //clsMBI.TwinPrime_Test();
            //clsMBI.PrimeTriplet_Test();
            //clsMBI.Mersenne2(23);
            clsMBI.ModPow_Misc_Stuff();
            //clsMBI.Pollard_Rho_Test();
            //clsMBI.RSA_Numbers();
            //clsMBI.Smooth_Nums_Test(N.ToString());

            Write("\nPress Enter: ");
            ReadLine();
        }
    }   // class
}   // namespace
