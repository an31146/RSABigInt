using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Globalization;
using System.IO;
using System.Numerics;
using System.Threading;
using System.Threading.Tasks;

using static System.Console;

#pragma warning disable IDE0011,IDE0055,IDE1006,IDE1005,IDE1017,CS0219,CS0168
#pragma warning disable IDE0049,IDE0051,IDE0060 
/*
 * IDE1006 Suppress Naming Rule Violation IDE1006
 * IDE1005 Delegate invocation can be simplified
 * IDE1017 Object initialization can be simplified
 * CS0168  The variable 'var' is declared but never used.
 * CS0219  The variable 'variable' is assigned but its value is never used
 * IDE0049 Name can be simplified
 * IDE0051 Private member 'member' is unused
 * IDE0060 Remove unused parameter
 */

namespace RSABigInt
{
	class MyBigInteger_Class
	{
		//private const uint ARRAY_SIZE = 0x166e0e21;
		private const uint ARRAY_SIZE = 0x8000000;
		private const uint LIMIT = 100000;
		private const int confidence = 15;

		private Random _randObj;
		private uint[] primes;               
		private uint[] factor_base;          //
											 // TO-DO: Make this a System.Collections.Generic.BitArray
		private uint[,] matrix;              // 2-dimensional matrix comprising of smooth num exponents mod 2
		Dictionary<BigInteger, Tuple<uint, List<BigInteger>>> partial_expos;

		private struct smooth_num
		{
			public BigInteger Q_of_x;
			public BigInteger save_Qx;
			public BigInteger x;
			public uint[] exponents;
			public string expo_str;
		};
		private smooth_num[] Qx;

		// constructor
		public MyBigInteger_Class()
		{
			_randObj = new Random((int)DateTime.Today.Ticks);
			primes = new uint[ARRAY_SIZE];                  // 131072 elements --- 0x18000000 = 1.5GB array
			factor_base = new uint[ARRAY_SIZE];
			prime_sieve(LIMIT);
		}

		public void prime_sieve(uint n)
		{
			uint p;
			primes.Initialize();

			Stopwatch sw = new Stopwatch();
			sw.Start();

			primes[0] = 2;
			for (p = 0; primes[p] < n; ) 
			{
				//Write("{0,8}", primes[p]);
				for (uint i = primes[p]*primes[p]; i < n; i += primes[p])
					primes[i] = 1;
				//Write($"{primes[p],8}");
				primes[++p] = primes[p-1] + 1;
				for (; primes[p] < n && primes[primes[p]] == 1; primes[p]++) ;     //find next prime (where s[p]==0)
			}
			//WriteLine();
			Array.Resize(ref primes, (int)p);

			//WriteLine($"{primes.Length} == {p}");

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

		public BigInteger RandPrime(int size, int conf = confidence)
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
				rnd |= _randObj.Next();
			}
			rnd |= 1;
			rem = BigInteger.ModPow(a, rnd - 1, rnd);

			while ( !(rem.IsOne || MillerRabin(rnd, conf)) )
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
			BigInteger twin = RandPrime(size: size);
			bool found = MillerRabin(twin, 2) && MillerRabin(twin + 2, 2);
			while (!found)
			{
				twin += 2;
				found = MillerRabin(twin, 2) && MillerRabin(twin + 2, 2);
			}
			
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
			int a_HalfLogXBase2 = BitCount(n) >> 1;
			BigInteger d = n >> a_HalfLogXBase2, q, _d;
			Stopwatch sw = new Stopwatch();

			int i = 0;
			sw.Start();
			//Newton's Method
			do
			{
				q = n / d + d;
				_d = d;
				q >>= 1;
				d = q;
				i++;
			} while (q * q > n);
			sw.Stop();

#if DEBUG
			WriteLine("iterations: {0}", i);
			WriteLine("\nSquareRoot({0})\nElapsed time: {1}\n", n, FormatTimeSpan(sw.Elapsed));
#endif
			Debug.Assert(q * q <= n);
			return q;
		}

		// Why is this function 3 times(!) quicker than the one above?  Number of operations used.
		// 10-Apr-20 Actually - difference is negligible, 1490s vs. 1497s
		public BigInteger Sqrt(BigInteger x)
		{
			int a_HalfLogXBase2 = BitCount(x) >> 1;
			BigInteger div = x >> a_HalfLogXBase2;
			BigInteger div2, y;
			Stopwatch sw = new Stopwatch();

			// Loop until we hit the same value twice in a row, or wind
			// up alternating.
			int i = 0;
			sw.Start();
			while (true)
			{
				div2 = BigInteger.Divide(x, div);
				y = BigInteger.Add(div, div2);
				y >>= 1;
				if (y.Equals(div) || y.Equals(div2))
					break;
				div = y;
				i++;
			}
			sw.Stop();
#if DEBUG
			WriteLine("iterations: {0}", i);
			WriteLine("\nSqrt({0})\nElapsed time: {1}\n", x, FormatTimeSpan(sw.Elapsed));
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

		public int BitCount(BigInteger n)
		{
			return (int)(BigInteger.Log(n, 2.0) + 0.5);
		}

		private uint[] GetPrimeFactors(BigInteger N)
		{
			uint [] factor_expos = new uint[factor_base.Length];
			for (int i = 0; i < factor_base.Length && !N.IsOne; i++)
			{
				uint j = 0, pr = factor_base[i];
				for (; (N % pr).IsZero; j++)    // divisble by prime in factor_base[]
					N /= pr;

				factor_expos[i] = j;
			}
			if (N == 1)         // smooth number with prime bound in factor_base
				return factor_expos;
			else
				return null;
		}

		private uint[] GetPrimeFactorsII(BigInteger N, BigInteger S)
		{
			if (BigInteger.GreatestCommonDivisor(N, S).IsOne)
				return null;
			
			uint[] factors = new uint[factor_base.Length];
			uint i = 0;
			foreach (uint pr in factor_base)
			{
				factors[i] = 0;
				BigInteger rem = BigInteger.Zero;
				BigInteger Q = BigInteger.DivRem(N, pr, out rem); 
				while (rem.IsZero)    // divisible by prime in factor_base[]
				{
					factors[i]++;
					N = Q;
					Q = BigInteger.DivRem(Q, pr, out rem);
					if (rem.IsZero)
						N = Q;
				}
				i++;

				if (N.IsOne)
					break;
			}
			if (N.IsOne)         // smooth number with prime bound in factor_base
				return factors;
			else
				return null;
			/*
				if (N < 5000)	// assume N is a prime
                {
					if (partial_expos.ContainsKey(N))
                    {
						ValueTuple<uint, List<BigInteger>> T2 = partial_expos[N].ToValueTuple();
						T2.Item1++;
						T2.Item2.Add(S);
						partial_expos[N] = T2.ToTuple();
					}
					else
					{
						partial_expos.Add(N, new Tuple<uint, List<BigInteger>>(1, new List<BigInteger> { S }));
					}
				}
			*/
		}

		private smooth_num[] GetPrimeFactors(List<smooth_num> Q1x)
		{
			smooth_num[] Qt = Q1x.ToArray();
			smooth_num[] QS1 = new smooth_num[Q1x.Count];
			int i = 0;

			CancellationTokenSource cts = new CancellationTokenSource();
			/*
			Parallel.For(0, QS.Length-1, new ParallelOptions() 
				{ MaxDegreeOfParallelism = 10, CancellationToken = cts.Token }, 
				(s) =>
				*/
			Parallel.ForEach(Q1x, new ParallelOptions()
				{ MaxDegreeOfParallelism = 10, CancellationToken = cts.Token },
				(QS) =>
			//for (int m = 0; m < Qt.Length; m++)
			{
				//for (int j = 0; j < factor_base.Length && !QS.save_Qx.IsOne; j++)
				//var QS = Qt[m];
				QS.exponents = new uint[factor_base.Length];
				int j = 0;
				QS.expo_str = "";
				foreach (uint pr in factor_base)
				{
					//uint pr = factor_base[j];
					while ((QS.save_Qx % pr).IsZero)    // divisible by prime in factor_base[]
					{
						QS.save_Qx /= pr;
						QS.exponents[j]++;
					}
#if DEBUG
					if (QS.exponents[j] > 0)
						QS.expo_str += String.Format("{0,5}^{1}", pr, QS.exponents[j]);
#endif
					j++;
					if (QS.save_Qx.IsOne)
						lock (QS1)
						{
							QS1[i] = QS;
							i++;
#if !DEBUG
							Debug.WriteLine(QS.expo_str);
#endif
							break;
						}
				}
				//Debug.WriteLine(String.Format("{0,5}", QS.save_Qx.IsOne));
				/*
				if (QS.save_Qx.IsOne)
				{
					lock (QS1)
					{
						//QS.exponents = GetPrimeFactors(QS.Q_of_x);
						QS1[i] = QS;
						i++;
						/*
						int q = 0;
						foreach (int m in QS.exponents)
						{
							if (m > 0)
								Write("{0,5}^{1} ", factor_base[q], m);
							q++;
						}
						WriteLine();

					}
				}
				*/
			});
			Array.Resize(ref QS1, i);
			GC.Collect();
			return QS1;
		}

		private void Factor_Base(BigInteger N)
		{
			int j = 0;
			foreach (uint pr in primes)
				if (Legendre(N, pr) == 1)                // add primes[i] to array if it is a quadratic reciprocal of N
				{
					factor_base[j++] = pr;
#if DEBUG
					Write("{0,8}", factor_base[j-1]);
#endif
				}
			Array.Resize(ref factor_base, j);
			WriteLine($"\nFactor base: {j} primes.\n");
		}

		private bool IsSmooth(BigInteger S, BigInteger pk)
		{
			BigInteger div = BigInteger.GreatestCommonDivisor(S, pk);
			int i = 0;
			while (!div.IsOne)
			{
				S /= div;
				i++;
				div = BigInteger.GreatestCommonDivisor(S, pk);
			}
#if DEBUG
			Debug.Write(String.Format("{0,6}\titerations: {1}\n", div.IsOne, i));
#endif
			return S.IsOne;         // smooth number with prime bound in factor_base
		}

		public int Legendre(BigInteger n, uint p)
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

		public int Legendre(uint n, uint p)
		{
			ulong p1, l = 1;

			// assumes p is an odd prime
			p1 = (p - 1) / 2;
			for (ulong i = 0; i < p1; i++) { 
				l *= n; l %= p;
			}

			if (l == 1)
				return 1;
			if (l == 0)
				return 0;
			else
				return -1;
		}

		public bool MillerRabin(BigInteger n, int k = confidence)
		{
			int[] base_primes = {
					2,   3,   5,   7,  11,  13,  17,  19,
					23,  29,  31,  37,  41,  43,  47,  53,
					59,  61,  67,  71,  73,  79,  83,  89,
					97, 101, 103, 107, 109, 113, 127, 131,
				137, 139, 149, 151, 157, 163, 167, 173,
				179, 181, 191, 193, 197, 199, 211, 223,
				227, 229, 233, 239, 241, 251, 257, 263, 
				269, 271, 277, 281, 283, 293, 307, 311
			};

			foreach (int p in base_primes)
				if (n % p == 0)
					return false;

			BigInteger r = n - 1;
			int s = 0;
			while (r.IsEven)
			{
				s++;
				r >>= 1;
			}

			if (k < 1) k = 1;
			else if (k > 64) k = 64;

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

			string str_bytes = "new byte [] {\n    ";
			int c = 0;
			foreach (byte b in reversed_bytes)
			{
				str_bytes += String.Format($"0x{b:x2}, ");
				c++;
				if (c % 8 == 0)
					str_bytes += "\n    ";
			}
			if (c % 8 == 0)
				str_bytes += "}";
			else
				str_bytes += "\n};";
			return str_bytes;
		}

		public string FormatTimeSpan(TimeSpan ts)
		{
			string strElapsed;
			if (ts.TotalMilliseconds < 1000.0d )
				strElapsed = String.Format("{0} ms", ts.Milliseconds);
			else
				strElapsed = String.Format("{0:F1} secs", ts.TotalSeconds);

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

		public void Mersenne()
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
			BigInteger P = RandPrime(100);
			BigInteger Q = RandPrime(100);
			BigInteger N = P * Q;
			BigInteger e = new BigInteger(0x10001);     // 65537 decimal
			BigInteger phiN = (P - 1) * (Q - 1);
			//WriteLine("GCD({0}, \n    {1}) = {2}\n", phiN.ToString(), N, BigInteger.GreatestCommonDivisor(phiN, N));

			BigInteger d = InverseMod(e, phiN);         // inverse modulus exists iff GCD(e, phiN) == 1

			WriteLine("RSA_Numbers()\n");
			WriteLine("P = {0}", P.ToString());
			WriteLine("Q = {0}", Q.ToString());
			WriteLine("N = {0}", N.ToString());
			WriteLine("e = {0}", e.ToString());
			WriteLine("d = {0}", d.ToString());

			BigInteger fib1 = Fibonacci(1223);
			BigInteger enc = BigInteger.ModPow(fib1, e, N);

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
			if (dec.Equals(fib1))
				WriteLine("<PASSED>.");
			//WriteLine("enc = {0}", enc.ToString());
			//WriteLine("dec = {0}\n", dec.ToString());
		}

		public void Sophie_Germain()
		{
			BigInteger p1 = RandPrime(23);
			//p1 = BigInteger.Parse("2458660187856824879520595114870378250951431099288225378935017566800781119530503250246319150383200577" +
			//                      "2239534362312959895639176940639315849312418626787213101575564785527284385424689741076546240829379542" + 
			//                      "7379986300689878537402008701959350545403526654541127010835528445689532162313465868838686033876428021" +
			//                      "28584806281635941597546342162000054644591515119");

			for (int i = 0; i < 2000; i++)
			{
				while ( !(MillerRabin(p1, 5) && MillerRabin(2 * p1 + 1, 5)) )
					p1 += 2;

				WriteLine($"{p1}");
				p1 += 2;
			}
			/*
			for (int i = 0; i < primes.Length/2; i++)
			{
				foreach (uint q in primes)
					if (2 * primes[i] + 1 == q)
					{
						Write($"{primes[i],8}");
						break;
					}
			}
			*/
						WriteLine();
	}

		public void ModPow_Misc_Stuff()
		{
			var N = RandPrime(size: 63);
			double Temp = BigInteger.Log10(N);
			int nbrPrimes = (int)Math.Exp(Math.Sqrt(Temp * Math.Log(Temp)) * 0.618);

			WriteLine("bitCount(N): {0}\n", BitCount(N));
			WriteLine("ByteArrayStruct({0}) = \n{1}\n", N, ByteArrayStruct(N.ToByteArray()));

			var T1 = BigInteger.Pow(new BigInteger(2), 1048576);                        // 315653 digit number!
			var T2 = (new BigInteger(1) << 9689) - 1;                                   // Should be a Mersenne prime.
			double LogT1 = BigInteger.Log10(T1);
			

			//StreamWriter file1 = new StreamWriter("output.txt", false);
			//file1.WriteLine(T1.ToString());
			//file1.Close();

			Stopwatch sw = new Stopwatch();
			BigInteger T3;
			sw.Start();
			{
				T3 = BigInteger.ModPow(new BigInteger(257), T2 - 1, T2);
			}
			sw.Stop();

			if (T3.IsOne)                                                                // This could take a few hours!
				WriteLine("ModPow time: {0}\n", FormatTimeSpan(sw.Elapsed));             // ModPow time: 12453 ms

			sw.Restart();
			{
				double LogT3 = BigInteger.Log10(T3);
			}
			sw.Stop();
			WriteLine("Log10(T3) elapsed time: {0} ms\n", sw.ElapsedMilliseconds);                 // ModPow time: 12453 ms

			string strNormalizedIntegerTwo = "2" + new String('0', 20000);
			WriteLine("strNormalizedIntegerTwo.GetHashCode(): 0x{0:X}", strNormalizedIntegerTwo.GetHashCode());
			//var sqrtTwo = SquareRoot(BigInteger.Parse(strNormalizedIntegerTwo));
			//WriteLine("{0}\n", sqrtTwo * sqrtTwo);

			//WriteLine(SquareRoot(BigInteger.Parse(strNormalizedIntegerTwo)) + "\n");
			//WriteLine(Sqrt(BigInteger.Parse(strNormalizedIntegerTwo)) + "\n");

			/*
			int n = 22291;    //13017;  //7921;   // 1789;   // 3607;
			WriteLine("fact({1}) = {0}\n", Factorial(n), n);
			WriteLine("fibonacci({1}) = {0}\n", Fibonacci(n), n);
			*/
		}

		public void ModPow_Misc_Stuff2()
		{

			var P1 = BigInteger.Parse("8949969815784082905285113653565030657117978813653332368993611264200624281180341263589905784897611545421273844719391941113720317582959695290277880367278839");
			bool bIsPrime = MillerRabin(P1);
			WriteLine($"MillerRabin({P1}): {bIsPrime}\nBitCount: {BitCount(P1)}\n");

			var P2 = new BigInteger(new byte[] {
				0x95, 0xe3, 0x5d, 0x14, 0xe5, 0x30, 0x1e, 0xbd,  0x76, 0x92, 0xa1, 0x26, 0xe7, 0xfa, 0xe2, 0xef,
				0xfd, 0x22, 0xea, 0xb7, 0x1b, 0x7e, 0xd2, 0x8d,  0x95, 0x38, 0x46, 0xb7, 0x67, 0xc2, 0xbb, 0xff,
				0x3a, 0x0f, 0xf9, 0x4e, 0x71, 0xcb, 0x4c, 0xe1,  0x23, 0xff, 0xab, 0xdf, 0x4f, 0x05, 0x4d, 0x86,
				0xa8, 0xd5, 0x0e, 0x0a, 0x81, 0xae, 0x16, 0x84,  0xb5, 0x08, 0x6b, 0xef, 0x68, 0x30, 0x01, 0xe7,
				0x00
			});

			bIsPrime = MillerRabin(P2);
			WriteLine($"MillerRabin({P2}): {bIsPrime}\nBitCount: {BitCount(P2)}\n");

			var P3 = new BigInteger(new byte[] {
				0x81, 0x3f, 0x9c, 0x81, 0x31, 0x78, 0x58, 0xa1,  0xcd, 0xbd, 0xdd, 0xdb, 0xc9, 0xa7, 0xb1, 0xcf,
				0x53, 0x92, 0x26, 0x80, 0x53, 0x89, 0xe5, 0x80,  0x26, 0x60, 0x23, 0x6a, 0x79, 0xc8, 0x1f, 0xf6,
				0xb2, 0x63, 0x87, 0x2e, 0x74, 0xe2, 0x6c, 0x0b,  0xfb, 0x2e, 0xb6, 0xe6, 0xa0, 0x02, 0xb1, 0x69,
				0x71, 0xc7, 0x47, 0xe9, 0x44, 0x9d, 0x43, 0x1a,  0x86, 0x39, 0xf5, 0x2a, 0x9b, 0xe8, 0x07, 0xda,
				0x00
			});

			/*
			P3 = new BigInteger(new byte[] {
				0x37, 0x61, 0x8c, 0x03, 0x96, 0xed, 0x2d, 0x2b,  0x59, 0x09, 0xea, 0xa7, 0xfd, 0x91, 0x95, 0x90, 
				0x57, 0x34, 0x73, 0x82, 0x31, 0x31, 0x06, 0x8b,  0xa4, 0x03, 0xe7, 0x3b, 0x58, 0x10, 0xf4, 0x08, 
				0xe9, 0x3c, 0x4b, 0x8f, 0x2e, 0xf3, 0xfa, 0x7f,  0x11, 0x90, 0xd6, 0xd2, 0x40, 0xc3, 0xa2, 0x45,
				0x8d, 0xa1, 0x56, 0x98, 0x6b, 0x7a, 0x04, 0x81,  0xd3, 0x50, 0x39, 0xe7, 0x32, 0xfe, 0x01, 0xf3,
				0x00
			});

			P3 = new BigInteger(new byte[]
			{
				0x9d, 0x4e, 0x78, 0x54, 0x43, 0x1e, 0x1f, 0xc8,  0x71, 0x42, 0x71, 0xbe, 0xc3, 0x26, 0x9e, 0xbe, 
				0xf4, 0x0b, 0x15, 0x5c, 0x52, 0x5a, 0x80, 0x00,  0x7a, 0x80, 0x56, 0x33, 0xe8, 0x42, 0x22, 0x3e, 
				0x50, 0x2f, 0xf7, 0x6a, 0xf7, 0x85, 0x13, 0xff,  0xd5, 0x93, 0xfd, 0x8b, 0x44, 0xc5, 0xf4, 0x10,
				0x97, 0x04, 0x5e, 0xd4, 0x17, 0x85, 0x47, 0xc2,  0xd5, 0xc1, 0xe0, 0xaf, 0x0e, 0x4f, 0x8a, 0x9e,
				0x00
			});
			*/
			bIsPrime = MillerRabin(P3);
			WriteLine($"MillerRabin({P3}): {bIsPrime}\nBitCount: {BitCount(P3)}\n");

			var P4a = new BigInteger(PseudoPrime4a());

			var P4b = new BigInteger(PseudoPrime4b());

			var P4c = new BigInteger(PseudoPrime4c());

			var P4d = new BigInteger(PseudoPrime4d());

			bIsPrime = MillerRabin(P4a);
			WriteLine($"MillerRabin({P4a}): {bIsPrime}\nBitCount: {BitCount(P4a)}\n");

			var P5 = new BigInteger(PseudoPrime5c());

			bIsPrime = MillerRabin(P5);
			WriteLine($"MillerRabin({P5}): {bIsPrime}\nBitCount: {BitCount(P5)}\n");

			var H1 = BigInteger.Parse("4c9a210dd08a0452cc8b31cab00f80a7f870553859f43739920453ccfa5e0e37acf0a0e60c728799" +
									   "a77fb60d325adf3bdcbeaa97670c5d29e24b917e49c3eaf0d7ccdb4afb479ced74a4c07a0028a860" +
									   "6e9724867be05bddce134a139694f18ff0ef9cf72aba5ac9de8a027a8ec5e618a69846968d692689" +
									   "cc92a253c7bce493ae089756d9d4c76d4fb8b3f3cfb9f61b800c37e9a19b4f89b729cfee1dd15816" +
									   "577bca01babe8c564a0bd2795b68880d3d67621d9444d1ac68b87f85b777b8247b10eef26c0c81f6" +
									   "d1a3ff49eab52b5261b3fe63f41e4cefa3367ce60389d0d10dafe1d1708eab1a4648547cbd777772" +
									   "3db2206895f36b1aa04522391bc3ea6c61ba2e253030fd523433713e5a64b27bbd7059855e08d346" +
									   "4bc3495b0a6867824a5201d68a47b7482e53e0a87e1cde253b67ccba18e4aa7810bf2e42f677d71a" +
									   "e2ae885131a0c43b777220158a38382b484be7c04fac0550a805f735acc372d3db09c495a5bbe9cc" +
									   "ad31553e111bc66d2ae2d711728f8782ca7fa2c65e5b51e819a0b0780ddf587ef0963d4ec80a4bf9a571dd", NumberStyles.HexNumber);
			bIsPrime = MillerRabin(H1);
			WriteLine($"MillerRabin({H1:x}): {bIsPrime}\nBitCount: {BitCount(H1)}\n");

			var H2 = BigInteger.Parse(
				"16ebe06bfcb56920ca13179c1f17bf2b791f590741bb963e81b65c3b893cfed4010ff65dbfb27aa6146cd1fa248ad4af853ac583db9ae52194eaa7" +
				"79a500e383b82c768f7a6f083956d3db263730fff36590acb6b6c9bb2c28ea13338bff209574c8a8a59a9a3eb1bb905ec55db409f2ba083d0049b6" +
				"bf1ccae07dc307cc2e8f185e4864edf982cefac692308c2896c1b88c61696f958702b2b3bc703bc26ed23318b2a8a82f9f8ba57ebdc19a90b5722f" +
				"2b86f642a7ed09534664f6fdaaa228656811385906ffdb356e2a216d77f85bb968e9e643ef689e391f3050374945e1b345ba34a178ed4088cbc46d" +
				"75381f284afe721b5ff5b56e958e7fba1a39694370d43e88842f178ec343401ff1b40ab01d08b7367b0bc6e95221d6d45d124d7038cfe7a9f5f355" +
				"c506d05927bba260e7267d7d3d7e3f47830abd919093554e13837d639c0079a24779dc5dac52524456308957f2c1792cef27704983c17d8c656f06" +
				"b3804ba3dba841314c524ba03f83a93ab415ea4133391fc7d5344241d9a031c02f965591943c99761f94135152218f334b8273dc8b4e070cbef76e" +
				"cc441384a0b92a8d410174668464b0b69d6822fc5783ec5343743d9ad022af7e9eae1399d9961d224f2da9da16be3b660bbc712273a3667ae1990d" +
				"6bb67a93b1c889d39dee02e3ae4fe6c1a4e0c3d8bcfe9bc003416a99583897ecc23fdd049b3ca302cc01a2360b702384aa739ea112c2916d1f9d81" +
				"235be91a2b2129ae84842886a0d17fb58959f35019f9b5ec765d1a31cffbdcb645483fad354d1b1486cb65ec3e17d0187f04c3789cca70ffa3fec7" +
				"47c4731fc73eb5ec61d13103af2aaf2f7f86a7b799d57a263c2ab370a63bf394b9cd5e2f38b5b672878056640448d0d693fa888d0c26797badbb8a" +
				"5a8c3c43d580e452d67f545b4ab737510f5f138b982064e66125c2028224c8844ec505fe8641d4f85e201d709e035e84118320baf9ad7071798902" +
				"f11c14d76bb3e2b0f3ee795601e417ae14f49ea0cf9e5b086f0ff6b33699e316630d75ec9e7f1b429f84749e9424992ff6432367d27b4b2daffdb4" +
				"60576f6915ae1eea17c1b18b892a9c78abed607b67d4f4edc2c79e274c5d275a3cb84144bea7fb", NumberStyles.HexNumber);
			bIsPrime = MillerRabin(H2);
			WriteLine($"MillerRabin({H2:x}): {bIsPrime}\nBitCount: {BitCount(H2)}\n");

		}

		//***********************************************************************
		// Tests the correctness of raising x to the power n
		// - using list of primes < 2000 and Pow()
		//***********************************************************************
		public void PowTest(int rounds)
		{
			BigInteger x;
			for (int count = 3; count < rounds; count++)
			{
				Write("Round: {0}", count);

				foreach (int p in primes)
				// foreach(int p in new int[] {2, 3, 5, 7, 11, 13, 17} )
				{
					if (p > 2000)
						break;

					BigInteger bigInt_p = new BigInteger(p);
					x = BigInteger.Pow(bigInt_p, count);

					//Console.WriteLine("\t{0}^{1} = {2}", p, count, x);

					if (count == 0 && x != new BigInteger(1))
						throw new ArithmeticException("x.Pow(0) was not equal to 1.");
					if (count == 1 && x != bigInt_p)
						throw new ArithmeticException("x.Pow(1) was not equal to x.");
					if (count > 0 && x % p != 0)
						throw new ArithmeticException(String.Format("x mod {0} was not congruent to zero.", p));
					if (p > 2 && (x % (p - 1) != 1))
						throw new ArithmeticException(String.Format("p^{0} mod (p-1) was not congruent to one.", count));
					if (BigInteger.GreatestCommonDivisor(x, new BigInteger(2017)) != 1)
						throw new ArithmeticException("gcd(x, 2017) has common denominator > 1.");

				}
				WriteLine(" <PASSED>.");
				// Console.ReadLine();

			}
		}

		public void SqrtTest2(int rounds)
		{
			BigInteger BigTwo = new BigInteger(256);

			for (int i = 0; i < 500; i++)       // 5 hundred million digits
				BigTwo *= 1000000;

			WriteLine(Sqrt(BigTwo));

			for (int count = 0; count < rounds; count++)
			{
				BigInteger y = new BigInteger(count + 1);
				for (int i = 0; i < 250; i++)
					y *= 1000000;

				BigInteger x = Sqrt(y);
				BigInteger z = (x + 1) * (x + 1);

				Write("Round: {0}", count);

				// check that x is the largest integer such that x*x <= z
				if (z <= y)
				{
					WriteLine("\nError at round " + count);
					WriteLine(x + "\n");
					return;
				}
				WriteLine(" <PASSED>.");
			}

			for (int count = 0; count < rounds; count++)
			{
				BigInteger p = RandPrime(5);
				BigInteger q = RandPrime(5);
				BigInteger N = p * q;
				BigInteger s = Sqrt(N);
				BigInteger z = (s + 1) * (s + 1);

				Write("Round: {0}", count);

				// check that x is the largest integer such that x*x <= z
				if (z <= N)
				{
					WriteLine("\nError at round " + count);
					WriteLine(s + "\n");
					return;
				}
				WriteLine(" <PASSED>.");
			}
		}

		private byte[] PseudoPrime4a()
		{
			return new byte[]
			{
				0xa9, 0xf0, 0xa0, 0x31, 0x1c, 0x50, 0x20, 0x00, 0xb0, 0xdb, 0xf6, 0x3a, 0x17, 0xf7, 0x40, 0xec, 
				0x01, 0xcc, 0xd5, 0xff, 0x17, 0xe3, 0x16, 0x81, 0xb9, 0x45, 0x1b, 0xa9, 0xd4, 0x2b, 0x59, 0x72, 
				0x66, 0x27, 0xc9, 0x63, 0x2f, 0xa5, 0x6a, 0xc3, 0xdf, 0x00, 0xbc, 0xb6, 0xe5, 0xa1, 0x31, 0xbc,
				0x60, 0xc6, 0x84, 0x37, 0x90, 0x17, 0x62, 0x5a, 0x19, 0x2c, 0x61, 0xc3, 0x7a, 0x78, 0x8a, 0x7b, 
				0x74, 0x14, 0x23, 0x24, 0x3c, 0x67, 0xf4, 0x5a, 0x31, 0x35, 0x1a, 0xe9, 0x44, 0x9b, 0x65, 0x66, 
				0x4a, 0x8e, 0x31, 0x02, 0x15, 0x1c, 0x10, 0xd6, 0xc5, 0x18, 0x8a, 0xef, 0x5f, 0xba, 0x6b, 0xad,
				0x3d, 0x8f, 0x26, 0x8a, 0x55, 0x62, 0x45, 0xcc, 0x5b, 0x5e, 0x39, 0xe4, 0xcc, 0x5c, 0x45, 0x77, 
				0x33, 0xc6, 0x41, 0x80, 0x84, 0x29, 0x75, 0x2a, 0xbc, 0xb5, 0x68, 0x50, 0xe0, 0x65, 0x65, 0x34, 
				0x2f, 0xbf, 0x57, 0xb8, 0x4e, 0x32, 0x9d, 0x4b, 0xf1, 0xf2, 0x94, 0x81, 0x10, 0xe7, 0x39, 0x5e,
				0x9d, 0x55, 0x14, 0xb6, 0xa5, 0xee, 0x4a, 0xca, 0xed, 0x42, 0x04, 0xca, 0x69, 0x86, 0xb4, 0xee, 
				0xbe, 0x5d, 0x95, 0x31, 0x94, 0x7a, 0x11, 0x0a, 0x00, 0xaa, 0x74, 0x1b, 0xc7, 0x2c, 0xf1, 0x95, 
				0x65, 0x20, 0xf6, 0xa2, 0x76, 0xa9, 0xa5, 0x6e, 0x56, 0x98, 0xe1, 0x74, 0x47, 0x90, 0x86, 0x9c,
				0x00,
			};
		}

		private byte[] PseudoPrime4b()
		{
			return new byte[] {
				0xe5, 0xc2, 0x65, 0x38, 0x8b, 0x3c, 0x76, 0x96,
				0x1b, 0x37, 0x86, 0xd0, 0xb9, 0x12, 0x01, 0x89,
				0x84, 0x8c, 0xdf, 0x7c, 0x6a, 0x9c, 0x94, 0x4f,
				0x07, 0x10, 0x4d, 0xb2, 0x1b, 0x94, 0xe5, 0xd9,
				0x09, 0xae, 0xf3, 0x97, 0x0c, 0xab, 0x14, 0x4d,
				0x27, 0x31, 0x93, 0x8f, 0x64, 0x9d, 0xd9, 0x37,
				0xb5, 0x49, 0x79, 0x82, 0x83, 0x81, 0x06, 0xaf,
				0x11, 0x10, 0xb1, 0xc2, 0xe2, 0x00, 0x0d, 0x0d,
				0x91, 0x86, 0x65, 0x87, 0xae, 0x67, 0xb9, 0x41,
				0x17, 0xe6, 0x6c, 0xe2, 0x19, 0xeb, 0x14, 0xcb,
				0x24, 0xa3, 0x29, 0x0f, 0x18, 0x91, 0xec, 0x5f,
				0x68, 0x2d, 0x5c, 0x6e, 0xe1, 0xb1, 0x5d, 0xa2,
				0x45, 0xb4, 0xce, 0xa6, 0xaf, 0xb9, 0x15, 0xdb,
				0x18, 0x46, 0x6a, 0x12, 0x78, 0x03, 0xb1, 0x43,
				0xd6, 0x00, 0x30, 0x39, 0xbe, 0x2e, 0x89, 0x54,
				0xd7, 0x60, 0x37, 0xfa, 0xdd, 0x51, 0x4f, 0x87,
				0x00,
			};
		}

		private byte[] PseudoPrime4c()
		{
			return new byte[]
			{
				0x9f, 0x59, 0x88, 0x44, 0xf6, 0xfa, 0x6c, 0x04, 
				0x9e, 0xe7, 0xee, 0x39, 0xd3, 0x3e, 0x62, 0x84, 
				0x39, 0xa2, 0x8a, 0xdb, 0xae, 0xdf, 0x67, 0x71,
				0x22, 0x5c, 0x1c, 0x4d, 0xf8, 0x96, 0xd2, 0x1b, 
				0x30, 0x2f, 0xd2, 0x4f, 0x8c, 0x4d, 0x77, 0x16, 
				0xbe, 0x77, 0xd2, 0x12, 0x84, 0xdc, 0x95, 0x2a,
				0x79, 0xfe, 0x6b, 0xf1, 0x7c, 0x44, 0xb4, 0x4a, 
				0x93, 0x33, 0x90, 0x8c, 0xa8, 0xd3, 0x1a, 0xa1,
				0x00,
			};
		}

		private byte[] PseudoPrime4d()
		{
			return new byte[]
			{
				0x93, 0xfd, 0x23, 0x7a, 0xaf, 0xf8, 0x34, 0x92, 
				0xbe, 0xc1, 0x9e, 0x5f, 0xe9, 0x30, 0x6c, 0xc8, 
				0xde, 0x7c, 0x12, 0x08, 0x15, 0x9c, 0x8b, 0xe2,
				0xe4, 0x63, 0xb9, 0x0c, 0xda, 0x42, 0x94, 0x2a, 
				0x39, 0xb8, 0x8e, 0xea, 0x9f, 0xad, 0x07, 0xf1, 
				0xd8, 0x1a, 0x3f, 0x28, 0xe3, 0xf2, 0xef, 0xd8,
				0x63, 0x66, 0x21, 0xe2, 0x82, 0xbb, 0x69, 0x06, 
				0x40, 0x52, 0xd3, 0x3d, 0xd5, 0x8c, 0x74, 0xc5,
				0x00,
			};
		}

		private byte[] PseudoPrime5()
		{
			return new byte[]
			{
				0x43, 0x50, 0x93, 0x0a,  0xb8, 0xe0, 0x4e, 0x36,  0x53, 0x63, 0x20, 0xdc,  0x7d, 0x32, 0x98, 0xfd, 
				0x85, 0x19, 0x91, 0xdd,  0x0e, 0x33, 0x39, 0x66,  0xfe, 0xc7, 0xf6, 0x1f,  0x53, 0xb0, 0xeb, 0xeb, 
				0x78, 0xe0, 0xb7, 0x74,  0x66, 0xb0, 0x60, 0x4b,  0x1b, 0x14, 0xcb, 0xd0,  0x53, 0x37, 0xbe, 0xca, 
				0x6e, 0xbe, 0x0d, 0x26,  0xe8, 0xcc, 0x76, 0x75,  0xbf, 0x87, 0x9b, 0xb4,  0xa5, 0x6f, 0xb8, 0xb3, 
				0x12, 0x22, 0x58, 0x50,  0xcf, 0x7b, 0xe7, 0xe4,  0x4a, 0x08, 0x96, 0x19,  0x77, 0xfb, 0x9f, 0x9f,
				0x7f, 0xaf, 0x46, 0xe0,  0xcb, 0x55, 0x6c, 0xa2,  0x0d, 0xc1, 0xfc, 0x9c,  0x99, 0x9c, 0x48, 0xca, 
				0x27, 0x48, 0xe2, 0x82,  0xa0, 0x71, 0xdb, 0x25,  0x67, 0xd3, 0xfd, 0xf4,  0x25, 0xbf, 0x51, 0xe8, 
				0x3b, 0xd8, 0xc5, 0xcb,  0x9c, 0x7b, 0x70, 0x3c,  0xce, 0xdf, 0x7f, 0x37,  0x8c, 0x60, 0xa0, 0x0f, 
				0xae, 0x80, 0x6c, 0x1f,  0x35, 0x11, 0x9a, 0xc8,  0x61, 0x84, 0x99, 0xe8,  0xaf, 0xcf, 0x58, 0xb6, 
				0x07, 0x1a, 0x44, 0xa2,  0x3e, 0x81, 0x75, 0x65,  0x48, 0x73, 0x36, 0x6d,  0xa8, 0xde, 0xb2, 0x65,
				0xd1, 0x88, 0xcb, 0xc3,  0x6f, 0x05, 0x72, 0xff,  0x88, 0xae, 0xf0, 0x47,  0xb4, 0xf8, 0x5b, 0x7a, 
				0x6a, 0xed, 0xfc, 0x61,  0x1f, 0xa2, 0xea, 0xe4,  0x78, 0xed, 0x79, 0x00,  0xf7, 0xd5, 0x52, 0xbf, 
				0x66, 0xc7, 0xce, 0x64,  0x4c, 0x88, 0xe0, 0x2d,  0xc6, 0x41, 0xd1, 0x23,  0x39, 0x2e, 0xf6, 0xbb, 
				0xbc, 0x12, 0xcc, 0x3e,  0x26, 0xf5, 0xbd, 0x26,  0xd6, 0x90, 0x2e, 0x28,  0x76, 0xfa, 0x26, 0x68, 
				0xab, 0x1f, 0x52, 0x99,  0xba, 0xc6, 0xd7, 0x11,  0x56, 0xea, 0xb5, 0x7a,  0xe5, 0xa7, 0xb5, 0xb7,
				0xa6, 0x5f, 0x3b, 0x71,  0xd8, 0x08, 0xa5, 0x37,  0x18, 0xd8, 0x25, 0x20,  0xdc, 0x64, 0x47, 0x38,
				0x98, 0xd0, 0xe0, 0x13,  0x8f, 0xb3, 0x2a, 0xc1,  0xa5, 0xb6, 0x51, 0xab,  0x38, 0xad, 0x73, 0x5d,
				0x87, 0x48, 0xdd, 0x8c,  0x0f, 0xb8, 0x42, 0xfe,  0x9e, 0x55, 0x74, 0x11,  0xd3, 0xa0, 0xe2, 0xea,
				0x86, 0x08, 0xb1, 0x77,  0xa1, 0x29, 0xe3, 0xb3,  0xa5, 0x72, 0xd4, 0xdb,  0x0f, 0xaa, 0xd4, 0xe0,
				0x42, 0xa7, 0x7b, 0x5a,  0x58, 0xc8, 0xa0, 0x22,  0x2e, 0xaf, 0x4b, 0x68,  0x07, 0xa6, 0xf7, 0x9d,
				0x28, 0x84, 0x61, 0x25,  0x70, 0xfd, 0xaa, 0x35,  0xbf, 0xf7, 0x82, 0x83,  0xef, 0x4f, 0xe5, 0x9d,
				0xd6, 0x39, 0x9f, 0x18,  0x94, 0xb1, 0x89, 0x7b,  0xcf, 0x4d, 0xd4, 0xd0,  0x87, 0x8b, 0xae, 0xf8,
				0x5f, 0x80, 0x6b, 0xa0,  0xeb, 0x89, 0x72, 0x80,  0x04, 0xb0, 0x06, 0x1d,  0x4d, 0x53, 0x6c, 0x90,
				0xe7, 0x96, 0xbf, 0xea,  0x63, 0xcb, 0x80, 0xb5,  0x01, 0x7f, 0x77, 0xf4,  0xf9, 0x7f, 0x26, 0x8c,
				0x57, 0x2d, 0x4c, 0xdf,  0xac, 0x49, 0xa9, 0x0f,  0x1c, 0x28, 0x7b, 0x66,  0xdb, 0x39, 0xd2, 0xa0,
				0x7a, 0xeb, 0x98, 0x39,  0x3f, 0x40, 0x06, 0xa3,  0x70, 0x8d, 0x75, 0x32,  0x56, 0x0f, 0x8c, 0x66,
				0xae, 0x32, 0x6c, 0x1c,  0xf2, 0xa0, 0xee, 0x38,  0xb2, 0x25, 0x45, 0x44,  0x1b, 0xe9, 0xe8, 0x8a,
				0x80, 0x82, 0xe9, 0x4a,  0xc6, 0xe6, 0x59, 0x47,  0x34, 0x53, 0xab, 0x0d,  0x52, 0x57, 0xb1, 0x76,
				0x8b, 0x17, 0x8c, 0xa9,  0x4f, 0x44, 0xbe, 0xdc,  0xbd, 0x23, 0x54, 0x92,  0x36, 0x62, 0x90, 0x3b,
				0x19, 0x11, 0x22, 0xb4,  0x29, 0x88, 0x40, 0x82,  0x06, 0x2b, 0xa8, 0x1f,  0x03, 0x1f, 0x57, 0x98,
				0xbf, 0x65, 0x56, 0xf0,  0x1d, 0x2b, 0xa3, 0xb2,  0xd9, 0x2c, 0x08, 0xbd,  0x9c, 0xbe, 0x6a, 0x0c,
				0x0b, 0x08, 0x3c, 0xe1,  0x51, 0x02, 0x08, 0x81,  0xec, 0x09, 0x23, 0x00,  0x23, 0x3d, 0x30, 0xc2,
				0x00,
			};
		}

		private byte[] PseudoPrime5a()
		{
			return new byte[] {
				0x6f, 0x96, 0x9b, 0x4f,  0x9c, 0x00, 0x7b, 0x64,  0x1c, 0x8d, 0x04, 0x34,  0x7f, 0xf8, 0x72, 0x2b,
				0x70, 0xd9, 0x67, 0x25,  0x13, 0x28, 0xb6, 0x45,  0x90, 0x0f, 0xa8, 0x4d,  0xab, 0x9b, 0x52, 0x59,
				0x9b, 0xce, 0x2e, 0x61,  0x01, 0x69, 0x8b, 0x45,  0x4d, 0x38, 0xa0, 0x59,  0xd5, 0xd1, 0xb7, 0x38,
				0x28, 0x6c, 0x63, 0x6d,  0xc8, 0x77, 0x63, 0x19,  0xa2, 0x55, 0x22, 0x5d,  0x11, 0x22, 0x31, 0x0b,
				0xe6, 0xd1, 0x2e, 0x1b,  0xe9, 0x5f, 0x18, 0x22,  0x57, 0x09, 0xc4, 0x10,  0x10, 0x5f, 0x3d, 0x78,
				0x11, 0xfe, 0xd3, 0x74,  0xad, 0x07, 0xa8, 0x05,  0xc3, 0x55, 0xfa, 0x0e,  0x17, 0x55, 0x94, 0x06,
				0x90, 0xf0, 0xdd, 0x39,  0xb0, 0x2c, 0x67, 0x16,  0x21, 0x14, 0xa6, 0x77,  0xb9, 0x16, 0x77, 0x18,
				0xb7, 0xff, 0x4d, 0x49,  0xb9, 0xd3, 0x06, 0x05,  0x1b, 0x12, 0xce, 0x10,  0x6d, 0xd9, 0x8e, 0x3b,
				0x85, 0x5c, 0xbc, 0x07,  0x6c, 0xf6, 0x6d, 0x17,  0x80, 0x1d, 0x35, 0x79,  0x55, 0x03, 0xd0, 0x1a,
				0x83, 0xfb, 0x8f, 0x1c,  0x7d, 0xfa, 0x83, 0x2c,  0xcb, 0x8a, 0xc0, 0x22,  0x4d, 0x79, 0x12, 0x5c,
				0xfb, 0x97, 0x78, 0x72,  0x89, 0x3b, 0x4a, 0x51,  0x28, 0x19, 0x17, 0x48,  0x11, 0xc7, 0x9c, 0x3d,
				0xa9, 0xfa, 0xcd, 0x33,  0xc2, 0xf8, 0xc2, 0x0c,  0x6f, 0xdc, 0xdb, 0x75,  0xa8, 0xaa, 0xa0, 0x47,
				0x79, 0x8c, 0xcd, 0x0a,  0x13, 0x32, 0x2a, 0x3b,  0x5f, 0xa3, 0x5e, 0x21,  0xee, 0xff, 0x07, 0x16,
				0x54, 0x5f, 0x48, 0x2a,  0x2b, 0xf6, 0x47, 0x7a,  0xdf, 0x6e, 0x01, 0x7e,  0x2f, 0x79, 0x72, 0x04,
				0x3f, 0xb8, 0x5b, 0x1d,  0x0d, 0x08, 0x7f, 0x48,  0xdb, 0x90, 0x00, 0x4f,  0x6e, 0x7a, 0xd2, 0x7e,
				0xcf, 0x85, 0xd6, 0x52,  0x85, 0x03, 0x95, 0x4d,  0x6f, 0xaa, 0x7e, 0x76,  0x04, 0x42, 0x70, 0xf0,
				0x00
			};
		}

		private byte[] PseudoPrime5b()
		{
			return new byte[] {
				0x11, 0xb3, 0xd8, 0x33, 0x3d, 0xd8, 0xf2, 0x02,  0x15, 0xf2, 0xcc, 0x53, 0x6b, 0x1d, 0x84, 0x47,
				0x8b, 0xa9, 0x21, 0x5f, 0x33, 0xe9, 0x46, 0x53,  0x56, 0x8a, 0xe5, 0x33, 0x87, 0x9c, 0x9c, 0x5b,
				0x83, 0x1a, 0x41, 0x3c, 0x7d, 0x0c, 0x80, 0x28,  0x13, 0xeb, 0x23, 0x17, 0xaf, 0x61, 0xd7, 0x2b,
				0x4c, 0x12, 0xb7, 0x02, 0xd3, 0xfa, 0x43, 0x1a,  0x7b, 0x94, 0xea, 0x5b, 0xef, 0x53, 0x72, 0x35,
				0xcc, 0x1d, 0xf3, 0x6f, 0x12, 0x41, 0x5b, 0x29,  0x31, 0x68, 0x31, 0x2b, 0xeb, 0xcc, 0xaf, 0x68,
				0x2e, 0xaf, 0x8d, 0x1d, 0xea, 0xa6, 0x68, 0x2d,  0x05, 0x90, 0x87, 0x6e, 0x66, 0x65, 0xde, 0x36,
				0xb5, 0x27, 0xcf, 0x37, 0xcd, 0xe7, 0x42, 0x68,  0xaf, 0xad, 0xba, 0x73, 0xc4, 0x05, 0xf9, 0x61,
				0xdf, 0xff, 0x0c, 0x30, 0x5c, 0x78, 0xb3, 0x36,  0x12, 0x52, 0x6e, 0x58, 0x68, 0xfa, 0x95, 0x78,
				0x12, 0x3d, 0x43, 0x43, 0x38, 0xf1, 0x63, 0x48,  0xe5, 0x8c, 0xbb, 0x46, 0xff, 0x5a, 0xab, 0x73,
				0x4f, 0x0a, 0xdf, 0x7c, 0xfb, 0xb3, 0xae, 0x69,  0x1a, 0x81, 0xb3, 0x64, 0xd1, 0xd2, 0xc4, 0x37,
				0x81, 0x19, 0x57, 0x7c, 0x35, 0x85, 0xee, 0x36,  0xbb, 0x41, 0x67, 0x06, 0x80, 0xa7, 0x34, 0x55,
				0xb5, 0x69, 0xd1, 0x4e, 0x43, 0x0c, 0x7f, 0x69,  0x49, 0xad, 0xe7, 0x44, 0x8b, 0x89, 0xad, 0x1b,
				0x9d, 0x29, 0x07, 0x04, 0xf3, 0xa3, 0x2f, 0x44,  0xc4, 0xbb, 0xb6, 0x39, 0x39, 0x81, 0xb1, 0x51,
				0xad, 0xe0, 0x13, 0x3f, 0x9f, 0x29, 0xc7, 0x76,  0x79, 0xc7, 0x06, 0x1f, 0xf1, 0x09, 0x09, 0x3d,
				0x97, 0xa2, 0xe1, 0x24, 0xab, 0x59, 0x40, 0x24,  0x4f, 0xeb, 0xd7, 0x21, 0x47, 0x3e, 0x10, 0x6a,
				0x81, 0xec, 0x22, 0x35, 0x26, 0xb1, 0x49, 0x34,  0x22, 0x84, 0x91, 0x58, 0x95, 0x47, 0xbe, 0xfb,
				0x00
			};
		}

		private byte[] PseudoPrime5c()
		{
			return new byte[] {
				0x33, 0xdf, 0x40, 0x5f, 0x24, 0x72, 0x3d, 0x04,  0x63, 0xd8, 0x92, 0x18, 0x2b, 0x49, 0xa8, 0x4c,
				0x3a, 0x72, 0x69, 0x66, 0x51, 0x4a, 0xa2, 0x79,  0x83, 0xc0, 0x7f, 0x36, 0xcd, 0x19, 0x5e, 0x0f,
				0x21, 0x26, 0xfd, 0x45, 0x2d, 0x24, 0x6d, 0x7b,  0x29, 0xda, 0xb5, 0x11, 0x17, 0x21, 0xc1, 0x56,
				0x68, 0x7f, 0x87, 0x61, 0xb1, 0x7e, 0xd9, 0x56,  0xbe, 0x14, 0xf9, 0x7e, 0x26, 0x72, 0x4f, 0x72,
				0x8a, 0xf7, 0x21, 0x71, 0xec, 0x0c, 0x3f, 0x23,  0x92, 0xba, 0x3e, 0x72, 0x1c, 0x9f, 0xd6, 0x6f,
				0x65, 0x24, 0xdf, 0x25, 0x55, 0xe2, 0xb3, 0x0c,  0x59, 0x97, 0xea, 0x10, 0x87, 0xbe, 0x8d, 0x5f,
				0x77, 0xa7, 0xc0, 0x66, 0xe1, 0x24, 0xe6, 0x64,  0x8d, 0x51, 0xae, 0x3c, 0xfb, 0xdb, 0xaa, 0x6b,
				0x01, 0xef, 0xf2, 0x12, 0xc7, 0xc4, 0x25, 0x69,  0xb9, 0x34, 0xe0, 0x7e, 0xe2, 0x81, 0x52, 0x5d,
				0x6f, 0x43, 0x7b, 0x56, 0x1a, 0x8d, 0x38, 0x73,  0x7d, 0xfa, 0xe4, 0x53, 0x35, 0x14, 0x58, 0x64,
				0xdb, 0xb5, 0x67, 0x05, 0x0e, 0x5f, 0xd6, 0x3d,  0xeb, 0x43, 0x3d, 0x65, 0x9b, 0x82, 0x9a, 0x62,
				0x6e, 0xb6, 0x57, 0x41, 0x2b, 0xa2, 0xd3, 0x07,  0x7e, 0xa6, 0xbe, 0x7e, 0xd4, 0xc3, 0x6f, 0x2b,
				0x63, 0x31, 0x37, 0x1b, 0xd7, 0xe1, 0x01, 0x3e,  0x68, 0xd1, 0x41, 0x6a, 0x52, 0x1c, 0xca, 0x50,
				0x1b, 0xf3, 0xe7, 0x1d, 0x95, 0x0a, 0x7a, 0x4e,  0x5b, 0xaf, 0xb4, 0x50, 0x75, 0x94, 0x0e, 0x47,
				0xb7, 0x6b, 0xbf, 0x32, 0xdf, 0x04, 0x10, 0x0a,  0x4b, 0x8e, 0x92, 0x40, 0x08, 0x75, 0x12, 0x08,
				0x93, 0xd5, 0x1d, 0x2e, 0xfd, 0xac, 0x55, 0x36,  0x5d, 0x5d, 0x40, 0x56, 0x5b, 0x00, 0x06, 0x04,  
				0x1b, 0x71, 0x14, 0x66, 0xc1, 0x81, 0x66, 0x14,  0x1d, 0x67, 0x67, 0x00, 0x87, 0xbe, 0x53, 0x88,                
				0x00
			};
		}

		public void Print_Legendre_Table(int a, int n)
		{
			Write("  a ");
			for (int i = 1; i <= a; i++)
				Write($"{i,4}");
			WriteLine("p   " + new String('-', 116));
			
			for (int j = 0; j < n; j++)
			{
				Write($"{primes[j],3} ");
				for (uint i = 1; i <= a; i++)
					Write("{0,4}", Legendre(i, primes[j]));
			}
			WriteLine("\n");
		}

		private BigInteger g (BigInteger x, BigInteger n, int a) 
		{
			BigInteger x_ = x * x + a;
			return BigInteger.Remainder(x_, n);
		}

		private Int64 gx (Int64 x, Int64 n, Int64 a)
		{
			return (x * x + a) % n;
		}

		public BigInteger Pollard_Rho(BigInteger n, int a)
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

		public void Pollard_Rho_Test(string semiPrime)
		{
			BigInteger N1 = BigInteger.Parse(semiPrime);
			// msieve factorized this 250-bit number in ~3mins.
			//N1 = BigInteger.Parse("923177721865685175285240199236472361656683591279028656230171797690188269779");

			//Pollard_Rho(8642411206451202301400009369343005291, 1) = 2007998171636555513 x 4303993563603435907
			//Time: 3250826 ms

			//N1 = BigInteger.Parse("20000000000000000672000000000000002907");
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

			WriteLine($"Pollard_Rho_Test({semiPrime})");
			sw.Start();
				BigInteger P1 = Pollard_Rho(N1, a);
			sw.Stop();
			
			BigInteger Q1 = N1 / P1;
			WriteLine("Pollard_Rho({0}, {3}) = {1} x {2}", N1, P1, Q1, a);
#if DEBUG
			string strValue = $"Pollard_Rho() Elapsed time: {FormatTimeSpan(sw.Elapsed)}\n";
			WriteLine(strValue);
#endif
		}

		private void Process_Matrix()
		{
			Stopwatch sw = new Stopwatch();

			matrix = new uint[factor_base.Length*2, factor_base.Length*3];
			// TO-DO: Parallelize the outer loop?  No, not worthwhile.
			sw.Start();
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

		private void Gauss_Elimination()
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
						WriteLine("\nSwap rows: {0} and {1}", p, i);
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
						Write("Add row: {0} to row: {1}\r", p, i);
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
			string strValue = $"\nRow adds: {row_adds}\nRow swaps: {row_swaps}\nElapsed time: {FormatTimeSpan(sw.Elapsed)}\n";
			WriteLine(strValue);
#endif
		}

		private void Dump_Matrix()
		{
			for (uint i = 0; i < matrix.GetLength(0); i++)                  // number of rows
			{
				Write("{0,3}: ", i);
				for (uint j = 0; j < matrix.GetLength(1); j++)              // number of columns
					Write("{0} ", matrix[i, j]);
				WriteLine();
			}
		}

		private void Calculate_Factors(BigInteger N1)
		{
			BigInteger P = BigInteger.Zero, Q = BigInteger.Zero;
			Stopwatch sw = new Stopwatch();
			sw.Start();
			DateTime dt0 = DateTime.Now;

			try
			{
				for (int i = matrix.GetLength(0) - 1; i >= 0; i--)                  // number of rows
				{
					bool bNonNullFound = false;
					for (int j = 0; j < factor_base.Length; j++)
						if (matrix[i, j] != 0)                                             // test for null vector
						{
							bNonNullFound = true;
							break;
							//loopState.Stop();
						}
					if (!bNonNullFound)
					{
						// calculate smooth number from exponents, should be a perfect square
						BigInteger x = BigInteger.One, y = BigInteger.One;
						for (int j = factor_base.Length; j < matrix.GetLength(1); j++)
							if (matrix[i, j] == 1)
							{
								x *= Qx[j - factor_base.Length].x;
								y *= Qx[j - factor_base.Length].Q_of_x;
							}
						if (!y.IsOne)               // Why is Sqrt(y) being called when y = 1?
						{
							BigInteger sqrt_y = Sqrt(y);
							uint[] expos = GetPrimeFactors(sqrt_y);
#if DEBUG
							for (uint m = 0; m < expos.Length; m++)
								if (expos[m] > 0)
									Write("{0,5}^{1} ", factor_base[m], expos[m]);
							WriteLine();
#endif
							y = x - sqrt_y;
							BigInteger P1 = BigInteger.GreatestCommonDivisor(N1, y);
							if (!P1.IsOne && P1.CompareTo(N1) != 0)
							{
								P = P1;
								Q = N1 / P1;
								throw new OperationCanceledException();
							}
						}
					}

				}      // for(...)
			}
			catch (OperationCanceledException ex)
			{
				WriteLine("\nFactors: {0}, {1}", P, Q);
				WriteLine("\nCaught exception: {0}", ex.Message);
				WriteLine("\nOperation cancelled, done.");
			}

			sw.Stop();
			DateTime dt1 = DateTime.Now;
#if DEBUG
			WriteLine("\nCalculate_Factors({0})\nElapsed time: {1}", N1, FormatTimeSpan(sw.Elapsed));
			WriteLine($"dt1 - dt0 = {dt1.Subtract(dt0).TotalSeconds:F1} s\n");
#endif
		}   // CalculateFactors

		private void Calculate_Factors_Task(BigInteger N1)
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
			// Collect smooth numbers
			Factor_Base(N1);
			BigInteger FB_Primorial = BigInteger.One;
			foreach (uint pr in factor_base)
				if (pr > 1000)
					FB_Primorial *= pr;

			BigInteger sqrt_N1 = SquareRoot(N1);
			Debug.Assert(sqrt_N1 * sqrt_N1 < N1);
			BigInteger i = sqrt_N1;
			BigInteger j = sqrt_N1;
			if (sqrt_N1.IsEven || i * i < N1)
			{
				i++;
				j--;
			}

			uint N_smooths = (uint)(factor_base.Length * 1.01d);
			if ((N_smooths & 1) == 1)
				N_smooths++;                // make it even
			Qx = new smooth_num[N_smooths];
			Qx.Initialize();
			uint k = 0;

			Stopwatch sw = new Stopwatch();
			sw.Start();

			List<Task> smooth = new List<Task>();
			smooth.Add(Task.Run(() =>
			{
				while (k < N_smooths)
				{
					BigInteger sm = i * i - N1;
					Debug.Assert(sm > 0);

					//if (IsSmooth(sm, FB_Primorial))
					if (!BigInteger.GreatestCommonDivisor(sm, FB_Primorial).IsOne)
					{
						uint[] expo1 = GetPrimeFactors(sm);
						if (expo1 != null)
						{
							Debug.Assert(expo1 != null);
							lock (Qx)
							{
								Qx[k].Q_of_x = sm;
								Qx[k].x = i;
								Qx[k].exponents = expo1;
								k++;
							}
							/*
							uint m = 0;
							foreach (uint e in expo1)
							{
								if (e > 0)
									Write("{0,5}^{1} ", factor_base[m], e);
								m++;
							}
							WriteLine();
							*/
							Write(k.ToString() + " smooth numbers\r");

						}
					}
					i++;
				}
			}));

			smooth.Add(Task.Run(() =>
			{
				while (k < N_smooths)
				{
					BigInteger sm = N1 - j * j;
					Debug.Assert(sm > 0);

					//if (IsSmooth(sm, FB_Primorial))
					if (!BigInteger.GreatestCommonDivisor(sm, FB_Primorial).IsOne)
					{
						uint[] expo1 = GetPrimeFactors(sm);
						if (expo1 != null)
						{
							Debug.Assert(expo1 != null);
							lock (Qx)
							{
								Qx[k].Q_of_x = sm;
								Qx[k].x = j;
								Qx[k].exponents = expo1;
								k++;
							}
							/*
							uint m = 0;
							foreach (KeyValuePair<uint, uint> expo in dict)
							{
								if (expo.Value > 0)
									Write("{0,5}^{1} ", expo.Key, expo.Value);
								m++;
							}
							WriteLine();
							*/
							Write(k.ToString() + " smooth numbers\r");

						}
					}
					j--;
				}
			}));

			Task.WaitAny(smooth.ToArray());

			sw.Stop();
			string strElapsed;
			if (sw.ElapsedMilliseconds <= 1000)
				strElapsed = String.Format("{0} ms", sw.ElapsedMilliseconds);
			else
				strElapsed = String.Format("{0:F1} s", (float)sw.ElapsedMilliseconds / 1000);

			WriteLine("\nCollected {0} smooth numbers.\nElapsed time: {1}\n", k, strElapsed);
			WriteLine("distances from sqrt_N1: {0}\t{1}", i - sqrt_N1, sqrt_N1 - j);
			WriteLine("{0:P8} of numbers found were smooth.", k / Math.Pow(10.0, BigInteger.Log10(i - j)));
			WriteLine("{0:F1} numbers/sec", k / sw.Elapsed.TotalSeconds);
		}

		public void Smooth_Numbers2(BigInteger N1)
		{
			BigInteger sqrt_N1 = Sqrt(N1);
			Debug.Assert(sqrt_N1 * sqrt_N1 < N1);
			// prime number factors
			Factor_Base(N1);
			BigInteger FB_Primorial = BigInteger.One;
			foreach (uint pr in factor_base)
				if (pr > 1000)
					FB_Primorial *= pr;

			BigInteger I = sqrt_N1 + 1;
			BigInteger J = sqrt_N1 - 1;

			uint N_smooths = (uint)(factor_base.Length * 1.02);
			if ((N_smooths & 1) == 1)
				N_smooths++;                    // make it even
			Qx = new smooth_num[N_smooths];     // class global scoped variable
			Qx.Initialize();

			//smooth_num[] Q1x = new smooth_num[N_smooths * N_smooths * 8];
			//Q1x.Initialize();
			List<smooth_num> Q1x = new List<smooth_num>();

			int k = 0;
			char[] spinners = new char[] { '|', '/', '-', '\\' };
			Stopwatch sw = new Stopwatch();

			sw.Start();
			// Collect smooth numbers - must be a better way than by trial division!
			//  https://en.wikipedia.org/wiki/Shanks%E2%80%93Tonelli_algorithm
			while (k < N_smooths)
			{
				//uint n = 0;
				Q1x.Clear();

				CancellationTokenSource cancellationSource = new CancellationTokenSource();
				ParallelOptions options = new ParallelOptions()
				{
					CancellationToken = cancellationSource.Token,
					MaxDegreeOfParallelism = 8
				};
				Parallel.For(0, N_smooths, options, (n) =>
				//while (n < N_smooths * N_smooths)
				{
					smooth_num sn = new smooth_num();
					lock(Q1x)
                    {
						sn.Q_of_x = N1 - J * J;
						Debug.Assert(sn.Q_of_x > 0);
						if (!BigInteger.GreatestCommonDivisor(sn.Q_of_x, FB_Primorial).IsOne)
						{
							sn.x = J;
							Q1x.Add(sn);
						}
						J -= 1;

						sn.Q_of_x = I * I - N1;
						Debug.Assert(sn.Q_of_x > 0);
						if (!BigInteger.GreatestCommonDivisor(sn.Q_of_x, FB_Primorial).IsOne)
						{
							sn.x = I;
							Q1x.Add(sn);
						}
						I += 1;
					}
				});

				Parallel.ForEach(Q1x, options, (Q1x_, loopState) =>
				{
					Debug.Assert(!BigInteger.GreatestCommonDivisor(Q1x_.Q_of_x, FB_Primorial).IsOne);
					{
						uint[] expos = GetPrimeFactors(Q1x_.Q_of_x);
						if (expos != null)
						{
							lock (Qx)
							try
							{
								Qx[k].Q_of_x = Q1x_.Q_of_x;			// save the smooth number 
								Qx[k].x = Q1x_.x;					// save the square root
								Qx[k].exponents = expos;			// save the prime exponents
								Write("{0}\r", spinners[k % 4]);
								k++;
							}
							catch (IndexOutOfRangeException ex)
							{
								WriteLine("Caught exception: {0}", ex.Message);
								loopState.Stop();
							}
						}
					}
				});
				
				//Write($"Collected {k} smooth numbers in {sw.Elapsed.TotalSeconds:F1} secs\r");
			}   // while (k < N_smooths) 
			sw.Stop();
#if DEBUG
			WriteLine("Collected {0} smooth numbers in {1}", k, FormatTimeSpan(sw.Elapsed));
			WriteLine("{0:P8} of numbers found were smooth.", k / Math.Pow(10.0, BigInteger.Log10(I - J)));
			WriteLine("{0:F1} numbers/sec", k / sw.Elapsed.TotalSeconds);
#endif
		}   // Smooth_Numbers2

		public void Smooth_Numbers3(BigInteger N1)
		{
			// prime number factors
			Factor_Base(N1);
			BigInteger FB_Primorial = BigInteger.One;
			foreach (uint pr in factor_base)
				if (pr > 1000)
					FB_Primorial *= pr;

			int N_smooths = (int)(factor_base.Length * 1.01d);
			if ((N_smooths & 1) == 1)
				N_smooths++;                    // make it even
			Qx = new smooth_num[N_smooths];     // class global scoped variable
			Qx.Initialize();

			BigInteger sqrt_N1 = SquareRoot(N1);
			Debug.Assert(sqrt_N1 * sqrt_N1 < N1);
			BigInteger I = sqrt_N1;
			BigInteger J = sqrt_N1;
			if (sqrt_N1.IsEven)
			{
				I++;
				J--;
			}

			int k = 0;
			const int numTasks = 2;
			List<Task> smooth_tasks = new List<Task>();
			List<smooth_num> Q1x;

			Stopwatch sw = new Stopwatch();
			sw.Start();
			while (k < N_smooths)
			{
				Stopwatch sw2 = new Stopwatch();
				Q1x = new List<smooth_num>();
				//int n = 0;
				sw2.Start();
				ParallelOptions options = new ParallelOptions() { MaxDegreeOfParallelism = 8 };
				Parallel.For(0, N_smooths * N_smooths, options, (n) =>
				//while (n < N_smooths * N_smooths)
				{
					smooth_num sn = new smooth_num();
					lock (Q1x)
					{
						sn.Q_of_x = N1 - J * J;
						//
						if (!BigInteger.GreatestCommonDivisor(sn.Q_of_x, FB_Primorial).IsOne)
						{
							sn.save_Qx = sn.Q_of_x;     // this is destroyed when factoring
							sn.x = J;
							Q1x.Add(sn);
						}
						J--;

						sn.Q_of_x = I * I - N1;
						//
						if (!BigInteger.GreatestCommonDivisor(sn.Q_of_x, FB_Primorial).IsOne)
						{
							sn.save_Qx = sn.Q_of_x;     // this is destroyed when factoring
							sn.x = I;
							Q1x.Add(sn);
						}
						I++;
					}
					//n += 2;
				});
				sw2.Stop();
				//WriteLine("Init Q1x: {0} ms", sw2.ElapsedMilliseconds);

				sw2.Restart();
				var Q2x = GetPrimeFactors(Q1x);
				sw2.Stop();
				//WriteLine("GetPrimeFactors(Q1x): {0} ms", sw2.ElapsedMilliseconds);
				//WriteLine("Q2x.Length: {0}", Q2x.Length);
				if (Q2x.Length > 0)
				{
					if (k + Q2x.Length > Qx.Length)
						Array.Resize(ref Qx, k + Q2x.Length);
					Q2x.CopyTo(Qx, k);
					k += Q2x.Length;
					Write($"Collected {k} smooth numbers in {sw.Elapsed.TotalSeconds:F1} secs\r");
				}
			}   // while (k < N_smooths) 
			sw.Stop();

			WriteLine("Collected {0} smooth numbers in {1}", k, FormatTimeSpan(sw.Elapsed));
			WriteLine("distances from sqrt_N1: {0}\t{1}", I - sqrt_N1, sqrt_N1 - J);
			WriteLine("{0:P8} of numbers found were smooth.", k / Math.Pow(10.0, BigInteger.Log10(I - J)));
			WriteLine("{0:F1} numbers/sec", k / sw.Elapsed.TotalSeconds);

			List<string> factor_expos = new List<string>();
			foreach (smooth_num S in Qx)
				factor_expos.Add(S.expo_str);
				
			factor_expos.Sort();
			foreach (string s in factor_expos)
				WriteLine(s);

		}   // Smooth_Numbers3

		public void Smooth_Numbers4(BigInteger N)
		{
			Factor_Base(N);

			BigInteger sqrt = Sqrt(N);
			Debug.Assert(sqrt * sqrt < N);

			BigInteger FB_Primorial = BigInteger.One;
			foreach (uint pr in factor_base)
			{
				if (pr > 2000)
					FB_Primorial *= pr;
			}

			uint N_smooths = (uint)(factor_base.Length * 1.02d);
			if ((N_smooths & 1) == 1)
				N_smooths++;                // make it even
			Qx = new smooth_num[N_smooths];
			Qx.Initialize();
			int k = 0;
			partial_expos = new Dictionary<BigInteger, Tuple<uint, List<BigInteger>>>();

			uint pr1 = factor_base[1] * factor_base[3];
			pr1 <<= 1;
			BigInteger B = sqrt;
			while (BigInteger.GreatestCommonDivisor(N - B * B, FB_Primorial).IsOne)
				B--;
			WriteLine("B: {0}\ndistance from sqrt: {1}", B, sqrt - B);
			WriteLine("GCD(sqrt, B): {0}", BigInteger.GreatestCommonDivisor(N - B * B, FB_Primorial));

			B = sqrt;
			while (!BigInteger.GreatestCommonDivisor(N - B * B, pr1).Equals(pr1))
				B--;
			WriteLine("B: {0}\ndistance from sqrt: {1}", B, sqrt - B);

			bool is_perfect = (N % 4 != 1);
			int x = 0, y = 0;
			uint A = factor_base[1], C = factor_base[3];
			WriteLine("is_perfect: {0}\nfactor base primorial: {1}\n", is_perfect, FB_Primorial);
			if (is_perfect)
			{
				//A *= factor_base[2];
				//C *= factor_base[4];
			}

			// Collect smooth numbers
			Stopwatch sw = new Stopwatch();
			sw.Start();

			List<Task> smooth = new List<Task>();
			smooth.Add(Task.Run(() =>
			{
				while (k < N_smooths)
				{
					BigInteger root = (A * x + B);
					BigInteger sN = root * root - N;
					Debug.Assert(sN % A == 0);
					
					uint[] expos = null;
					expos = GetPrimeFactorsII(sN, FB_Primorial);
					if (expos != null)
					{
						/*
						int i = 0;
						foreach (uint e in expos)
						{
							if (e > 0)
								Write("{0,5}^{1} ", factor_base[i], e);
							i++;
						}
						WriteLine();
						*/
						Write('.');
						lock (Qx)
						{
							Qx[k].Q_of_x = sN;
							Qx[k].x = root;
							Qx[k].exponents = expos;
							Interlocked.Increment(ref k);
						}
					}
                    Interlocked.Increment(ref x);
                    //Interlocked.Add(ref x, 2);
				}
			}));

			smooth.Add(Task.Run(() =>
			{
				while (k < N_smooths)
				{
					BigInteger root = (A * C * x + B);
					BigInteger sN = root * root - N;
					Debug.Assert(sN % (A * C) == 0);

					uint[] expos = null;
					expos = GetPrimeFactorsII(sN, FB_Primorial);
					if (expos != null)
					{
						/*
						int i = 0;
						foreach (uint e in expos)
						{
							if (e > 0)
								Write("{0,5}^{1} ", factor_base[i], e);
							i++;
						}
						WriteLine();
						*/
						Write('/');
						lock (Qx)
						{
							Qx[k].Q_of_x = sN;
							Qx[k].x = root;
							Qx[k].exponents = expos;
							Interlocked.Increment(ref k);
						}
					}
                    Interlocked.Increment(ref x);
                    //Interlocked.Add(ref x, 2);
                }
			}));

			smooth.Add(Task.Run(() =>
			{
				while (k < N_smooths)
				{
					BigInteger root = (C * y + B);
					BigInteger sN = N - root * root;
					Debug.Assert(sN % C == 0);

					uint[] expos = null;
					expos = GetPrimeFactorsII(sN, FB_Primorial);
					if (expos != null)
					{
						/*
						int i = 0;
						foreach (uint e in expos)
						{
							if (e > 0)
								Write("{0,5}^{1} ", factor_base[i], e);
							i++;
						}
						WriteLine();
						*/
						Write('?');
						lock (Qx)
						{
							Qx[k].Q_of_x = sN;
							Qx[k].x = root;
							//WriteLine(Qx[k].x);
							Qx[k].exponents = expos;
							Interlocked.Increment(ref k);
						}
					}
					Interlocked.Decrement(ref y);
					//Interlocked.Add(ref y, -2);
				}
			}));

			smooth.Add(Task.Run(() =>
			{
				while (k < N_smooths)
				{
					BigInteger root = (A * y + B);
					BigInteger sN = N - root * root;
					Debug.Assert(sN % A == 0);

					uint[] expos = null;
					expos = GetPrimeFactorsII(sN, FB_Primorial);
					if (expos != null)
					{
						/*
						int i = 0;
						foreach (uint e in expos)
						{
							if (e > 0)
								Write("{0,5}^{1} ", factor_base[i], e);
							i++;
						}
						WriteLine();
						*/
						Write('+');
						lock (Qx)
						{
							Qx[k].Q_of_x = sN;
							Qx[k].x = root;
							Qx[k].exponents = expos;
							Interlocked.Increment(ref k);
						}
					}
					Interlocked.Decrement(ref y); 
					//Interlocked.Add(ref y, -2);
				}
			}));

			Task.WaitAny(smooth.ToArray());

			sw.Stop();
			string strElapsed;
			if (sw.ElapsedMilliseconds <= 1000)
				strElapsed = String.Format("{0} ms", sw.ElapsedMilliseconds);
			else
				strElapsed = String.Format("{0:F1} s", (float)sw.ElapsedMilliseconds / 1000);

			WriteLine("\nCollected {0} smooth numbers.\nElapsed time: {1}\n", k, strElapsed);
			WriteLine("{0:P8} of numbers found were smooth.", k / Math.Pow(10.0, BigInteger.Log10(x - y)));
			WriteLine("{0:F1} numbers/sec\n{1}", k / sw.Elapsed.TotalSeconds, new String('-', 100));

			List<BigInteger> extra_primes = new List<BigInteger>(partial_expos.Keys);
			extra_primes.Sort();
			
			/*
			foreach (BigInteger key in extra_primes)
				if (partial_expos[key].Item1 == 2)
                {
					WriteLine("prime counts: {0,5}\t{1}", key, partial_expos[key].Item1);
					BigInteger inv_mod = InverseMod(key, N);
					WriteLine(String.Format("InverseMod({0}, {1}) = {2}\n", key, N, inv_mod));
					WriteLine("Q1: {0}\nQ2: {1}", partial_expos[key].Item2[0], partial_expos[key].Item2[1]);
					BigInteger sqr = BigInteger.Pow(partial_expos[key].Item2[0] * partial_expos[key].Item2[1] * inv_mod, 2);
					WriteLine("SquareRoot({0}) = {1}\n{2}", sqr, SquareRoot(sqr), new String('-', 100));
				}
			*/
		}   // Smooth_Numbers4

		public void Quadratic_Sieve(string S1)
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
			double logN = BigInteger.Log(N);
			WriteLine("Log(N): {0:F12}", logN);
			uint sieve_max = (uint)Math.Exp(Math.Sqrt(logN * Math.Log(logN)) * 0.55);        // twiddle-factor
			WriteLine("sieve_max: {0}", sieve_max);
			primes = new uint[ARRAY_SIZE];
			prime_sieve(sieve_max);

            // original Smooth_Numbers only uses 2 threads (Tasks)!
            //Smooth_Numbers(N);
            // Parallel.For implementation
            //Smooth_Numbers2(N);
            // Parallel.For now within GetPrimeFactors function
            //Smooth_Numbers3(N);
            // using list of tasks with multiples of prime factor in root
            Smooth_Numbers4(N);
#if DEBUG
            Write("Press Enter: ");
			ReadLine();
#endif
			Process_Matrix();
			//Dump_Matrix();
			Gauss_Elimination();
			//Dump_Matrix();
			Calculate_Factors(N);
			//Calculate_Factors_Task(N);
		}

	}   // class MyBigInteger_Class

	class Program
	{
		static void Main(string[] args)
		{
			MyBigInteger_Class clsMBI = new MyBigInteger_Class();

			BigInteger p = clsMBI.RandPrime(2);
			BigInteger q = clsMBI.RandPrime(2);
			BigInteger N = p * q;

			WriteLine($"{p} x {q} = {N}\n");

			//clsMBI.TwinPrime_Test();                              // outputs to twin_primes.txt
			//clsMBI.PrimeTriplet_Test();
			//clsMBI.Mersenne();
			//clsMBI.Mersenne2(23);
			//clsMBI.ModPow_Misc_Stuff();
			//clsMBI.Pollard_Rho_Test(N.ToString());
			//clsMBI.PowTest(1000);
			//clsMBI.Print_Legendre_Table(29, 31);
			//clsMBI.RSA_Numbers();
			//clsMBI.Sophie_Germain();
			clsMBI.Quadratic_Sieve(N.ToString());
			//clsMBI.SqrtTest2(1000);

			Write("\nPress Enter: ");
			ReadLine();
		}
	}   // class
}   // namespace
