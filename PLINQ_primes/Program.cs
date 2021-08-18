using System;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;

using static System.Console;

#pragma warning disable IDE0005,IDE1006
//  IDE0005 Using directive is unnecessary
//  IDE1006 Suppress Naming Rule Violation IDE1006
namespace PLINQ_primes
{
    public class Program
    {
        private static BitArray prime_bits;
        private const int LIMIT = 10000000;
        private static List<int> _primes;

        static void sieve(int S)
        {
            int i, j;
            BitArray bits = new BitArray(S + 1);
            bits.SetAll(false);

            for (i = 2; i < Math.Sqrt(S); i++)
            {
                for (j = i * i; j <= S; j += i)
                    bits[j] = true;
            }

            _primes = new List<int> { 2 };

            for (j = 3; j <= S; j++)
                if (!bits[j])
                {
                    _primes.Add(j);
                }
        }

        static bool is_prime(int N)
        {
            int sqrt_N = (int)Math.Sqrt(N);

            // 2 is a prime
            if (N == 2)
                return true;
            // test if even
            if ((N & 1) == 0)
                return false;
            // start trial division at _primes[1] = 3
            for (int i = 1; i < _primes.Count && _primes[i] <= sqrt_N; i++)
                if (N % _primes[i] == 0)        // _primes[i] divides N
                    return false;
            return true;
        }

        public static void Main(string[] args)
        {
            int limit = LIMIT;
            if (args.Length == 1)
                limit = int.Parse(args[0]);

            sieve(limit);

            //for (int i = 2147395600; i < int.MaxValue; i++)
            //    if (is_prime(i))
            //        Write("{0,12}", i);
            //WriteLine();

            IEnumerable<int> numbers = Enumerable.Range(2, limit);
            var parallelQuery =
                from n in numbers.AsParallel()
                    //where Enumerable.Range(2, (int)Math.Sqrt(n)).All(i => n % i > 0)
                where is_prime(n)
                select n;

            Stopwatch sw1 = new Stopwatch();
            sw1.Start();
            int[] primes = parallelQuery.ToArray();
            sw1.Stop();

            WriteLine("\n primes.Length: {0}", primes.Length);
            WriteLine("\n1. Elapsed time: {0} ms", sw1.ElapsedMilliseconds);

            prime_bits = new BitArray(limit);
            prime_bits.SetAll(false);

            int count = 0;
            sw1.Restart();
            //foreach (var e in parallelQuery)
            foreach (int n in primes)
            {
                //Write("{0,12}", n);
                prime_bits.Set(n, true);
                count++;
            }
            sw1.Stop();

            WriteLine("\nprimes: {0}", count);
            WriteLine("\n2. Elapsed time: {0} ms", sw1.ElapsedMilliseconds);
            Write("\nPress Enter: ");
            ReadLine();
        }
    }
}
#pragma warning restore IDE1006

/*
Sun 09/03/2017 10:54:35
C:\Google Drive\Projects\RSABigInt\PLINQ_primes\bin\Debug\netcoreapp1.1>"\Program Files\dotnet\dotnet.exe" exec PLINQ_primes.dll 1000000000


1. Elapsed time: 367735 ms

primes: 50847534


2. Elapsed time: 448 ms

Press Enter:
*/

/*
C:\Google Drive\Projects\RSABigInt\PLINQ_primes>dotnet exec bin\Debug\netcoreapp2.2\PLINQ_primes.dll 420000000

 primes.Length: 22344479

1. Elapsed time: 175623 ms

primes: 22344479

2. Elapsed time: 234 ms

Press Enter:

*/

/*
18/08/2021 19:01:27
C:\Google Drive\Projects\RSABigInt\PLINQ_primes\bin\Release\netcoreapp5.0>PLINQ_primes.exe 1000000000

 primes.Length: 50847534

1.Elapsed time: 176943 ms

primes: 50847534

2.Elapsed time: 264 ms

Press Enter:
*/
