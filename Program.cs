using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Text;
using System.Numerics;
using System.Reflection;
using System.Threading;
using System.Threading.Tasks;

namespace RSABigInt
{
    class MyBigInteger_Class
    {
        Random _randObj;
        uint[] primes = new uint[0x20000];               // 131072 elements --- 0x18000000 = 1.5GB array
        uint[] factor_base = new uint[0x20000];          //
        struct smooth_num
        {
            public BigInteger Q;
            public uint[] exponents;
        };
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
        }

        public void prime_sieve(ulong n)
        {
            int p;
            primes.Initialize();

            primes[0] = 2;
            for (p = 0; primes[p] <= n;) 
            {
                for (ulong i = primes[p]*primes[p]; i <= n; i+=primes[p])
                    primes[i] = 1;
                primes[++p] = primes[p-1] + 1;
                for (; primes[p] <= n && primes[primes[p]] == 1; primes[p]++) ; //find next prime (where s[p]==0)
            }
            Array.Resize(ref primes, p);
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

            //Newton's Method
            do
            {
                q = n / d + d;
                q /= 2;
                d = q;
            } while (q*q > n);
    
            return q;
        }

        public BigInteger Factorial(int n)
        {
            BigInteger fact = BigInteger.One;

            for (int i = 2; i <= n; i++)
                fact *= i;

            return fact;
        }

        uint[] GetPrimeFactors(BigInteger N)
        {
            uint [] factor_expos = new uint[factor_base.Length];

            for (uint i=0; i<factor_base.Length; i++)
            {
                uint j;
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
                    //Console.Write(factor_base[j] + "\t  ");
                    factor_base[j++] = primes[i];
                }
            Array.Resize(ref factor_base, j);
            Console.WriteLine("Factor base: {0} primes.", j);
        }

        public void Smooth_Numbers(string str1)
        {
            BigInteger N1 = BigInteger.Parse(str1);
            BigInteger sqrt_N1 = SquareRoot(N1);
            BigInteger i = sqrt_N1 + 1;
            BigInteger j = sqrt_N1 - 1;

            // Collect smooth numbers
            Factor_Base(N1);
            smooth_num[] Qx = new smooth_num[factor_base.Length];

            Qx.Initialize();
            long k = 0;
            sw1.Restart();

            Task[] smooth = new Task[2];
            smooth[0] = Task.Run(() =>
            {
                while (k < factor_base.Length)
                {
                    BigInteger sm = i * i - N1;
                    uint[] expo1 = GetPrimeFactors(sm);
                    if (expo1 != null)
                    {
                        Qx[k].exponents = expo1;
                        Qx[k].Q = sm;
                        Interlocked.Increment(ref k);
                        Console.Write(k.ToString() + " smooth numbers\r");
                    }
                    i++;
                }
            });

            smooth[1] = Task.Run(() =>
            {
                while (k < factor_base.Length)
                {
                    BigInteger sm = N1 - j * j;
                    uint[] expo1 = GetPrimeFactors(sm);
                    if (expo1 != null)
                    {
                        Qx[k].exponents = expo1;
                        Qx[k].Q = sm;
                        Interlocked.Increment(ref k);
                        Console.Write(k.ToString() + " smooth numbers\r");
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
            
            Console.WriteLine("Collected {0} smooth numbers.\nElapsed time: {1}\n", k, strElapsed);
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
                        Console.WriteLine("{0}\n{1}\n{2}\n", X.ToString(), (X + 2).ToString(), (X + 6).ToString());
                    else
                        if (MillerRabin(X + 4, 2))
                            Console.WriteLine("{0}\n{1}\n{2}\n", X.ToString(), (X + 4).ToString(), (X + 6).ToString());
        }

        public void TwinPrime_Test()
        {
            for (BigInteger X = TwinPrime(12); ; X += 2)
                if (MillerRabin(X, 2) && MillerRabin(X + 2, 2))
                    Console.WriteLine("{0}\n{1}\n", X.ToString(), (X + 2).ToString());
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
                        Console.WriteLine("M[{0}] = {1}", primes[i], strPow2Sub1);
                    else
                        Console.WriteLine("M[{0}] = {1}...{2}", primes[i], strPow2Sub1.Substring(0, 12), strPow2Sub1.Substring(strPow2Sub1.Length - 12, 12));
                    x++;
                    //Console.WriteLine("elapsed time: {0} ms\n", sw1.ElapsedMilliseconds);
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

        // Use LucasLehmer to determine if 2^n-1
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
                        Console.WriteLine("M[{0}] = {1}", primes[i], strPow2Sub1);
                    else
                        Console.WriteLine("M[{0}] = {1}...{2}", primes[i], strPow2Sub1.Substring(0, 12), strPow2Sub1.Substring(strPow2Sub1.Length - 12, 12));
                    x++;
                    Console.WriteLine("elapsed time: {0} ms\n", sw1.ElapsedMilliseconds);
                    sw1.Restart();
                }
                if (n < x)
                    break;
            }
        }

        public void RSA_Numbers()
        {
            BigInteger P = RandPrime(3);
            BigInteger Q = PrimeTriplet(3);
            BigInteger N = P * Q;
            BigInteger e = new BigInteger(65537);
            BigInteger phiN = (P - 1) * (Q - 1);
            //Console.WriteLine("GCD({0}, \n    {1}) = {2}\n", phiN.ToString(), N, BigInteger.GreatestCommonDivisor(phiN, N));

            BigInteger d = InverseMod(e, phiN);

            Console.WriteLine("RSA_Numbers()\n");
            Console.WriteLine("P = {0}", P.ToString());
            Console.WriteLine("Q = {0}", Q.ToString());
            Console.WriteLine("N = {0}", N.ToString());
            Console.WriteLine("e = {0}", e.ToString());
            Console.WriteLine("d = {0}", d.ToString());

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
            Console.WriteLine("enc = {0}", enc.ToString());
            Console.WriteLine("dec = {0}\n", dec.ToString());
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
            Console.WriteLine("ModPow time: {0} ms\n", sw1.ElapsedMilliseconds);                // ModPow time: 12453 ms
            double LogT2 = BigInteger.Log10(T2);
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
 
	        while (h == 1) {
		        count = 1;
 
		        while (count <= cycle_size && h == 1) {
                    x = g(x, n, a);
			        //x = gx(Int64.Parse(x.ToString()), Int64.Parse(n.ToString()), a);
                    //Console.WriteLine("x = {0}", (x-x_fixed).ToString());
			        count++;
			        h = BigInteger.GreatestCommonDivisor(x - x_fixed, n);
                    //Console.WriteLine("h = {0}", h.ToString());
		        }
 
		        if (h != 1)
			        break;
 
		        cycle_size *= 2;
                Console.WriteLine("cycle_size = {0,-8}\tx = {1}", cycle_size, x);
		        x_fixed = x;
	        }
            Console.WriteLine("count = {0}\n", count);
        	return h;
        }

        public void Pollard_Rho_Test()
        {
            BigInteger N1;
            // msieve factorized this 250-bit number in ~3mins.
            //N1 = BigInteger.Parse("923177721865685175285240199236472361656683591279028656230171797690188269779");

            N1 = BigInteger.Parse("1152656570285234495703667671274025629");     // Time: 2358867 ms     Time: 1873793 ms
            //N1 = BigInteger.Parse("462717344089999398416479");                  // Time: 2639 ms    Time: 2416 ms
            //N1 = BigInteger.Parse("12923855417829126637");                    // 20-digits - i.e. GE than 64-bits.
            //N1 = BigInteger.Parse("3369738766071892021");
            //N1 = BigInteger.Parse("4607863703200169");
            //N1 = BigInteger.Parse("139078421707568423");
            //N1 = BigInteger.Parse("87256236345731407");
            //N1 = BigInteger.Parse("373463523233483");
            //N1 = BigInteger.Parse("135723676817");
            //N1 = new BigInteger(21530071);
            //N1 = new BigInteger(12546257);
            const int a = 1;

            Console.WriteLine("Pollard_Rho_Test()");
            sw1.Restart();
            BigInteger P1 = Pollard_Rho(N1, a);
            sw1.Stop();
            
            BigInteger Q1 = N1 / P1;
            Console.WriteLine("Pollard_Rho({0}, {3}) = {1} x {2}", N1, P1, Q1, a);
            Console.WriteLine("Time: {0} ms\n", sw1.ElapsedMilliseconds);
        }

        public void Smooth_Nums_Test()
        {
            //Smooth_Numbers("21818232425302600378616644247667406319");
            //Smooth_Numbers("10218568504117913286880427471505442091");             // 7551.6 s fb = 6055 primes
            //Smooth_Numbers("1152656570285234495703667671274025629");              // 2888.0 s fb = 1086 primes        2567.8 s fb = 1593 primes       2613.5 s fb = 1803 primes       2693.4 s fb = 2200 primes       3103.5 s fb = 6059 primes 
            //Smooth_Numbers("3851667332709411289323864692105059");                 // 1528.2 s fb = 1801 primes         1617.0 s fb = 1018 primes        1409.1 s fb = 1018 primes
            //Smooth_Numbers("43272494503935639032000984197");                      // 163.0 s  fb = 610 primes         149.5 s  fb = 715 primes          165.3 s fb = 740 primes         394.2 s fb = 4814 primes        601.8 s fb = 6075 primes
            //Smooth_Numbers("990632981767960443643259");                           // 20.0 s   fb = 154 primes
            //Smooth_Numbers("462717344089999398416479");                           // 5.9 s    fb = 269 primes
            //Smooth_Numbers("3369738766071892021");
            Smooth_Numbers("802846957519667581");
        }
    }   // class MyBigInteger_Class

    class Program
    {
        static void Main(string[] args)
        {
            MyBigInteger_Class c = new MyBigInteger_Class();

            c.prime_sieve(10003);
            //Console.WriteLine("sqrt(2) = {0}\n", c.SquareRoot(BigInteger.Parse("2" + new String('0', 800))));
            //Console.WriteLine("fact(1789) = {0}\n", c.Factorial(1789).ToString());

            Assembly assem = typeof(BigInteger).Assembly;
            BigInteger p = (BigInteger)assem.CreateInstance("System.Numerics.BigInteger");

            //c.TwinPrime_Test();
            //c.PrimeTriplet_Test();
            //c.Mersenne2(23);
            //c.Smooth_Nums_Test();
            //c.RSA_Numbers();
            //c.ModPow_Misc_Stuff();
            c.Pollard_Rho_Test();

            Console.Write("\nPress Enter: ");
            Console.ReadLine();
        }
    }   // class
}   // namespace
