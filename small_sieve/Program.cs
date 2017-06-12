using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;


namespace small_sieve
{
    class Program
    {
        const uint number_of_small_primes = 6541;
        static uint[] small_primes = new uint[number_of_small_primes];
        static uint[] small_sieve = new uint[1024];
        static uint small_base;

        //
        // count the number of zeros
        //

        static uint count_zero_bits(uint[] addr, uint size)
        {
            uint[] data = new uint[256];
            byte[] addr_bytes = new byte[4096];
            uint i, j, k;

            if (data[1] == 0)
                for (i = 0; i < 256; i++)
                    for (j = i ^ 255; j != 0; j >>= 1)
                        if ( (j & 1) == 1)
                            data[i]++;

            for (i = 0; i < size; i += 4)
            {
                k = i >> 2;
                addr_bytes[i] = (byte)addr[k];
                addr_bytes[i + 1] = (byte)(addr[k] >> 8);
                addr_bytes[i + 2] = (byte)(addr[k] >> 16);
                addr_bytes[i + 3] = (byte)(addr[k] >> 24);
            }

            j = 0;
            for (i = 0; i < size; i++)
            {
                j += data[addr_bytes[i]];
                //Console.Write("{0,8}", addr_bytes[i]);
            }
            return j;
        }

        static void update_small_sieve()
        {
            uint i, j;

            if (small_primes[0] == 0)
            { 
                // initialize the small_primes array
                for (j = 0; j < 1024; j++)
                    small_sieve[j] = 0;
                for (i = 3; i < 256; i += 2)
                    if ((small_sieve[i >> 6] & (1U << (int)((i >> 1) & 31))) == 0)
                        for (j = (i * i) >> 1; j < 32768; j += i)
                            small_sieve[j >> 5] |= 1U << (int)(j & 31);
                j = 0;
                for (i = 3; i < 65536; i += 2)
                    if ((small_sieve[i >> 6] & (1U << (int)((i >> 1) & 31))) == 0)
                        small_primes[j++] = i;
                if (j != number_of_small_primes)
                    return; // this should never happen
            }
            for (j = 0; j < 1024; j++)
                small_sieve[j] = 0;
            for (i = 0; i < number_of_small_primes; i++)
            {
                j = small_primes[i] * small_primes[i];
                //Console.Write("{0,8}", j);
                if (j >= small_base + 65536)
                    break;
                if (j < small_base)
                {
                    j = small_base / small_primes[i];
                    j *= small_primes[i];
                    if (j < small_base)
                        j += small_primes[i];
                    if ((j & 1) == 0)
                        j += small_primes[i];
                }
                for (j = (j - small_base) >> 1; j < 32768; j += small_primes[i])
                    small_sieve[j >> 5] |= 1U << (int)(j & 31);
            }
        }
        static void test_small_sieve()
        {
            uint pc, i, j;

            pc = 0;
            small_base = 0;
            i = 1000000;
            while (small_base < 10000000)
            {
                update_small_sieve();
                j = (i - small_base) >> 4;
                if (j > 4096)
                    j = 4096;
                //Console.WriteLine($"pc = {pc}");
                pc += count_zero_bits(small_sieve, j);
                if (small_base + (j << 4) == i)
                {
                    Console.WriteLine("{0,9} {1}", i, pc);
                    i += 1000000;
                }
                if (j < 4096)
                    pc += count_zero_bits(small_sieve, 4096 - j);
                small_base += 65536;
            }
        }

        static void Main(string[] args)
        {
            test_small_sieve();
            Console.Write("Press Enter: ");
            Console.ReadLine();
        }
    }
}
