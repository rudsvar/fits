fn fizzbuzz(n: Int): String = if n % 3 == 0 && n % 5 == 0 then "FizzBuzz" else if n % 3 == 0 then "Fizz" else if n % 5 == 0 then "Buzz" else "";
println(fizzbuzz(15));
