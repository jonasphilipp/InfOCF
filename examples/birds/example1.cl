signature
   p,b,f

conditionals
example1{
   (f | b),     // birds usually fly
   (!f | p),    // penguins usually do not fly
   (!f | b,p),  // penguins which are also birds usually do not fly
   (b | p)      // penguins are usually birds
}
