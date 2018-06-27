using System;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics;

namespace segmented_sieve
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
        static void segmented_sieve(Int64 limit, int segment_size = L1D_CACHE_SIZE)
        {
            int sqrt = (int)Math.Sqrt((double)limit);
            //double twin_prime_const = 1.0d;
            Int64 count = (limit < 2) ? 0 : 1;
            int s = 2;
            int n = 3;

            // vector used for sieving
            BitArray segment = new BitArray(segment_size);

            // generate small primes <= sqrt
            BitArray is_prime = new BitArray(sqrt + 1, true);
            for (int i = 2; i * i <= sqrt; i++)
                if (is_prime[i])
                    for (int j = i * i; j <= sqrt; j += i)
                        is_prime[j] = false;

            List<int> primes = new List<int>();
            List<int> next = new List<int>();

            for (int low = 0; low <= limit; low += segment_size)
            {
                segment.SetAll(true);

                // current segment = interval [low, high]
                Int64 high = low + segment_size - 1 < limit ? low + segment_size - 1 : limit;

                // store small primes needed to cross off multiples
                for (; s * s <= high; s++)
                    if (is_prime[s])
                    {
                        primes.Add(s);
                        next.Add(s * s - low);
                    }

                // segmented sieve of Eratosthenes
                for (int i = 1; i < primes.Count; i++)
                {
                    int j = next[i];
                    for (int k = primes[i] * 2; j < segment_size; j += k)
                        segment[j] = false;
                    next[i] = j - segment_size;
                }
                for (; n <= high; n += 2)
                    count += segment[n - low] ? 1 : 0;
                    /*if (segment[n - low])
                    {
                        Console.WriteLine("{0,10}", n);
                        count++;
                        //twin_prime_const *= 1.0d - 1.0d / (double)((n - 1) * (n - 1));
                    }*/
            }

            Console.WriteLine("\n\n{0} primes found.", count);
            //cout << "twin prime constant: " << twin_prime_const << endl;
        }
        static void Main(string[] args)
        {
            // generate the primes below this number
            Int64 limit = 100000000;
            Stopwatch clock = new Stopwatch();

            if (args.Length >= 1)
                limit = Int64.Parse(args[0]);

            int size = L1D_CACHE_SIZE;
            if (args.Length >= 2)
                size = Int32.Parse(args[1]);

            clock.Start();
            segmented_sieve(limit, size);
            clock.Stop();

            Console.WriteLine("sieve time: {0} ms.\n", clock.ElapsedMilliseconds);
            Console.Write("Press Enter: ");
            Console.ReadLine();
        }
    }
}
