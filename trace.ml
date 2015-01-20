type rule = string

type step_id = string
	      
type step =
  | Step of step_id * rule * step_id list * Smt2d.Abstract.term list
