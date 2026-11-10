import HelloWorld

open BaseLang
open CheckedLang

def outl := String.append "OUT: "

def poutl (n : String) := IO.println (outl n)

def main : IO Unit := do
  poutl s!"Compute"
