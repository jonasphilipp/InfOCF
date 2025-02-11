signature
    a,b,c,d,e,f
conditionals
simple {
        (b|a),
        (c|b),
        (e|d),
        (f|e),
        (a|f),
        (!f|!a),
        (!f|!a,Top),
        (!f|!a;Bottom)
        }
// abusing comments literally just to mess with your 'parse intelligently' method.cl
