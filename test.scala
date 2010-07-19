
object Test {

def f(x: Int) : Int = 
  if (x < 1) 1 else g(x) + g(x - 1)

def g(x: Int) : Int = 
  if (x < 1) 1 else f(x-1) + f(x-2)

}
