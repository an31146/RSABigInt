using System;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics;
using System.Threading.Tasks;

using static System.Console;

namespace segmented_sieve_v2
{
    class Program
    {
        /// @file   segmented_sieve.cpp
        /// @author Kim Walisch, <kim.walisch@gmail.com> 
        /// @brief  This is a simple implementation of the segmented sieve of
        ///         Eratosthenes with a few optimizations. It generates the
        ///         primes below 10^9 in 0.8 seconds (single-threaded) on an
        ///         Intel Core i7-4770 CPU (3.4 GHz) from 2013.
        ///         This is free software released into the public domain.

        const int L1D_CACHE_SIZE = 32768;

        /// Generate primes using the segmented sieve of Eratosthenes.
        /// This algorithm uses O(n log log n) operations and O(sqrt(n)) space.
        /// @param limit         Sieve primes <= limit.
        /// @param segment_size  Size of the sieve array in bytes.
        ///
        static void segmented_sieve(int limit, int segment_size = L1D_CACHE_SIZE)
        {
            int sqrt = (int)Math.Sqrt((double)limit);
            //double twin_prime_const = 1.0d;
            long count = (limit < 2) ? 0 : 1;

            // generate small primes <= sqrt
            BitArray is_prime = new BitArray(limit+1, true);
            for (int i = 2; i * i < sqrt; i++)
            {
                if (is_prime[i])
                    for (int j = i * i; j <= sqrt; j += i)
                        is_prime[j] = false;
            }

            List<int> primes = new List<int>();
            for (int i = 2; i < sqrt; i++)
            {
                if (is_prime[i])
                {
                    primes.Add(i);
                }
            }

            // Note to self - parallelizing this doesn't help, 39s vs. 13s for single thread.
            ParallelOptions options = new ParallelOptions();
            options.MaxDegreeOfParallelism = 2;
            Parallel.ForEach(primes, options, (int l) =>
            {
                lock (is_prime)
                {
                    for (int i = l * l; i <= limit; i += l)
                        is_prime[i] = false;
                }
            });

            Parallel.For(sqrt, limit, options, (int i) =>
            {
                if (is_prime[i])
                    lock (primes)
                    {
                        primes.Add(i);
                    }
            });
            WriteLine("\n\n{0} primes found.", primes.Count);

            //cout << "twin prime constant: " << twin_prime_const << endl;
        }
        static void Main(string[] args)
        {
            // generate the primes below this number
            int limit = 1000000000;
            Stopwatch clock = new Stopwatch();

            if (args.Length >= 1)
                limit = int.Parse(args[0]);

            int size = L1D_CACHE_SIZE;
            if (args.Length >= 2)
                size = int.Parse(args[1]);

            clock.Start();
            segmented_sieve(limit, size);
            clock.Stop();

            WriteLine("sieve time: {0} ms.\n", clock.ElapsedMilliseconds);
            Write("Press Enter: ");
            ReadLine();
        }
    }
}
