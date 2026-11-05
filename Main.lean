import HelloWorld

def outl := String.append "OUT: "

def poutl (n : String) := IO.println (outl n)

def main : IO Unit := do
  poutl s!"Hello, {hello} {incr 5} {double 5} {double_if_pow2 2} {double_if_pow2 3}!"
  poutl s!"Waah"
  poutl s!"Compute"

