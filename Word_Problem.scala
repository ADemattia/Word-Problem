import lisa.automation.Substitution.ApplyRules as Substitution
import lisa.automation.Tableau
import scala.util.Try


object Word_Problem extends lisa.Main {

  val x = variable
  val y = variable
  val z = variable
  val w = variable
  val t = variable

  // least and upper 
  val zero = ConstantTermLabel("zero", 0)
  addSymbol(zero)
  val one = ConstantTermLabel("one", 0)
  addSymbol(one)

  // Signature of ortholattices
  val <= = ConstantPredicateLabel.infix("<=", 2) 
  addSymbol(<=)
  val u = ConstantFunctionLabel.infix("u", 2) // join 
  addSymbol(u)
  val n = ConstantFunctionLabel.infix("n", 2) // meet 
  addSymbol(n)
  val ne = ConstantFunctionLabel("ne", 1) // negation
  addSymbol(ne)
  
  extension (left: Term) {
    def <=(right: Term): Formula = (Word_Problem.<= : ConstantPredicateLabel[2])(left, right)
    infix def u(right: Term): Term = (Word_Problem.u: ConstantFunctionLabel[2])(left, right)
    infix def n(right: Term): Term = (Word_Problem.n: ConstantFunctionLabel[2])(left, right)
    def ne: Term = (Word_Problem.ne: ConstantFunctionLabel[1])(left)
    def zero: Term = (Word_Problem.zero)
    def one: Term = (Word_Problem.one)
  }

  // Equivalent Axiomatization of ortholattice
  val reflexivity = Axiom(x <= x)
  val antisymmetry = Axiom(((x <= y) /\ (y <= x)) ==> (x === y))
  val def_equ = Axiom((x === y) ==> ((x <= y) /\ (y <= x)))
  val transitivity = Axiom(((x <= y) /\ (y <= z)) ==> (x <= z))
  val P4 = Axiom((x n y) <= x)
  val P5 = Axiom((x n y) <= y)
  val P6 = Axiom(((x <= z) /\ (x <= y)) ==> (x <= (y n z)))
  val P4p = Axiom(x <= (x u y))
  val P5p = Axiom(y <= (x u y))
  val P6p = Axiom(((x <= z) /\ (y <= z)) ==> ((x u y) <= z))
  val P7 = Axiom(x <= ne(ne(x)))
  val P7p = Axiom(ne(ne(x)) <= x)
  val P8 = Axiom((x <= y) ==> (ne(y) <= ne(x)))
  val NC = Axiom((x <= ne(x)) ==> (x <= y))
  val P3 = Axiom(zero <= x)
  val P3p = Axiom(x <= one)

  // deletable 
  val P9 = Axiom((x n ne(x)) <= zero)
  val P9p = Axiom(one <= (x u ne(x))) 


  val noz = Theorem(ne(one) <= zero) {
     have(thesis) by Backward_Proof.solve

  }
  val doubleNegationEquality = Theorem(ne(ne(x)) === x) {
    have(thesis) by Tautology.from(P7, P7p, antisymmetry of (y := ne(ne(x))))
  }

  val EX1 = Theorem((z n ne(z)) <= zero) {
    have(thesis) by Tautology.from(P9 of (x := z))
  }

  val EXTO = Theorem(one <= (x n (ne(x) u y)) |- one <= y) {
    val step = have(one <= (x n (ne(x) u y)) |- one <= x) by Tautology.from(P4 of (y := (ne(x) u y)), transitivity of (x := one, y := (x n (ne(x) u y)), z := x))
    val step1 = have(one <= (x n (ne(x) u y)) |- ne(x) <= zero) by Tautology.from(step, P8 of (x := one, y := x), noz, transitivity of (x := ne(x), y := ne(one), z := zero))
    val step2 = have(one <= (x n (ne(x) u y)) |- ne(x) <= y) by Tautology.from(step1, reflexivity of (x := y), P3 of (x := y), transitivity of (x := ne(x), y := zero, z := y))
    val step3 = have(one <= (x n (ne(x) u y)) |- (ne(x) u y) <= y) by Tautology.from(step2, P6p of (x := ne(x), z := y), reflexivity of (x := y))
    val step4 = have(one <= (x n (ne(x) u y)) |- (x n (ne(x) u y)) <= y) by Tautology.from(step3, P5 of (y := (ne(x) u y)), transitivity of (x := (x n (ne(x) u y)), y := (ne(x) u y), z := y))
    have(thesis) by Tautology.from(step4, transitivity of (x := one, y := (x n (ne(x) u y)), z := y))
  }

  import lisa.prooflib.ProofTacticLib.ProofTactic
  import lisa.prooflib.Library

  object Backward_Proof extends ProofTactic {
    def solve(using lib: library.type, proof: lib.Proof)(goal: Sequent): proof.ProofTacticJudgement = {
      if goal.right.size != 1 
       then proof.InvalidProofTactic("Backward_Proof can only be applied to solve goals of the form (s1 <= t1, s2 <= t2, ..., sn <= tn) |- s <= t")
      else { // Starting the proof of goal

        def extractRelevantTerm(goal: Sequent): Set[Word_Problem.Term] = {
          val formula_set = goal.left ++ goal.right
          var relevant_term: Set[Word_Problem.Term] = Set()

          for (elem <- formula_set) {
            val elem_af = elem.asInstanceOf[AtomicFormula]
            val left = elem_af.args.head
            val right = elem_af.args.tail.head
            relevant_term = relevant_term + left
            relevant_term = relevant_term + right
          }

          def extract(set: Set[Word_Problem.Term], elem: Word_Problem.Term): Set[Word_Problem.Term] = {
            var output_set = set
            if elem.label == Word_Problem.ne then {
                val a = elem.args.head
                output_set = set + a
                return extract(output_set, a)
              }

            if elem.label == n then {
              val a = elem.args.head
              val b = elem.args.tail.head
              output_set = output_set + a
              output_set = output_set + b
              return (extract(output_set, a) ++ extract(output_set, b))
              }

            if elem.label == u then {
              val a = elem.args.head
              val b = elem.args.tail.head
              output_set = output_set + a
              output_set = output_set + b
              return (extract(output_set, a) ++ extract(output_set, b))
              }

              return output_set
          }

          def extractKnownTerm(set: Set[Word_Problem.Term]): Set[Word_Problem.Term] = {
            var known_term = set
            for (elem <- set) {
             known_term = extract(known_term, elem)
            }
            return known_term
          }

          def addComplementedTerm(set: Set[Word_Problem.Term]): Set[Word_Problem.Term] = {
            var complemented_term = set
            for (elem <- set) {
              complemented_term = complemented_term + (Word_Problem.ne(elem))
              complemented_term = complemented_term + (Word_Problem.ne(Word_Problem.ne((elem))))
            }
            return complemented_term
          }

          val known_term = extractKnownTerm(relevant_term)
          return addComplementedTerm(known_term)
        }

        val relevant_term = extractRelevantTerm(goal)
        val axiom_set = goal.left
        var axiom_term: Set[Term] = Set()
        var proven_sequent: Set[proof.ValidProofTactic] = Set()
        var visited_sequent: Set[Sequent] = Set()

        for(elem <- axiom_set) {
          var new_goal = Sequent(goal.left, Set(elem))
          val s1 = have(new_goal) by Restate
          proven_sequent = proven_sequent + s1.judgement.asInstanceOf[proof.ValidProofTactic]
        }

        def prove(goal: Sequent): proof.ProofTacticJudgement = {
          //Check in proven_sequent
          for (elem <- proven_sequent) {
            if elem.bot == goal then {
              val s1 = have(goal) by Tautology.from(have(elem))
              return s1.judgement
            }
          }
          
          //Check in visited_sequent
          if visited_sequent.contains(goal) then {
            return proof.InvalidProofTactic("The inequality is not true in general")
          } else {
            visited_sequent = visited_sequent + goal

            val formula = goal.right.head.asInstanceOf[AtomicFormula]
            val left = formula.args.head
            val right = formula.args.tail.head

            // 0-premises checks
            // Reflexivity
            if left == right then {
              val s1 = have(goal) by Tautology.from(reflexivity of (x := left))
              proven_sequent = proven_sequent + s1.judgement.asInstanceOf[proof.ValidProofTactic]
              return s1.judgement
            }

            
            // Axiom P7 : x <= ne(ne(x))
            if right == Word_Problem.ne(Word_Problem.ne(left)) then {
              val s1 = have(goal) by Tautology.from(P7 of (x := left))
              proven_sequent = proven_sequent + s1.judgement.asInstanceOf[proof.ValidProofTactic]
              return s1.judgement
            }

            // Axiom P7': ne(ne(x)) <= x
            if left == Word_Problem.ne(Word_Problem.ne(right)) then {
              val s1 = have(goal) by Tautology.from(P7p of (x := right))
              proven_sequent = proven_sequent + s1.judgement.asInstanceOf[proof.ValidProofTactic]
              return s1.judgement
            }

            // Axiom P3 - least element : 0 <= x 
            if left == zero then {
              val s1 = have(goal) by Tautology.from(P3 of (x := right))
              proven_sequent = proven_sequent + s1.judgement.asInstanceOf[proof.ValidProofTactic]
              return s1.judgement
            }

            // Axiom P3' - least element : x <= 1
            if right == one then {
              val s1 = have(goal) by Tautology.from(P3p of (x := left))
              proven_sequent = proven_sequent + s1.judgement.asInstanceOf[proof.ValidProofTactic]
              return s1.judgement
            }

            // recursive checks
            // Axiom P8 : x <= y => ne(y) <= ne(x)
            if left.label == Word_Problem.ne && right.label == Word_Problem.ne then {
              val a = left.args.head
              val b = right.args.head
              var new_goal_1 = Sequent(goal.left, Set(b <= a))
              val s1 = prove(new_goal_1)
              if s1.isValid then {
                val s3 = have(goal) by Tautology.from(have(s1), P8 of (x := b, y := a))
                proven_sequent = proven_sequent + s3.judgement.asInstanceOf[proof.ValidProofTactic]
                return s3.judgement
              }
            }

            // Axioms P4 - P5: x n y <= x, x n y <= y 
            if left.label == n then {
              val a = left.args.head
              val b = left.args.tail.head
              var new_goal_1 = Sequent(goal.left, Set(a <= right))
              val s1 = prove(new_goal_1)
              if s1.isValid then {
                val s3 = have(goal) by Tautology.from(have(s1), P4 of (x := a, y := b), transitivity of (x := left, y := a, z := right))
                proven_sequent = proven_sequent + s3.judgement.asInstanceOf[proof.ValidProofTactic]
                return s3.judgement
              }
              var new_goal_2 = Sequent(goal.left, Set(b <= right))
              val s2 = prove(new_goal_2)
              if s2.isValid then {
                val s3 = have(goal) by Tautology.from(have(s2), P5 of (x := a, y := b), transitivity of (x := left, y := b, z := right))
                proven_sequent = proven_sequent + s3.judgement.asInstanceOf[proof.ValidProofTactic]
                return s3.judgement
              }
            }

            // Axiom P6' : x <= z & y <= z => x u y <= z 
            if left.label == u then {
              val a = left.args.head
              val b = left.args.tail.head
              var new_goal_1 = Sequent(goal.left, Set(a <= right))
              val s1 = prove(new_goal_1)
              if s1.isValid then {
                var new_goal_2 = Sequent(goal.left, Set(b <= right))
                val s2 = prove(new_goal_2)
                if s2.isValid then {
                  val s3 = have(goal) by Tautology.from(have(s1), have(s2), P6p of (x := a, y := b, z := right))
                  proven_sequent = proven_sequent + s3.judgement.asInstanceOf[proof.ValidProofTactic]
                  return s3.judgement
                }
              }
            }

            // Axiom P6 : x <= y & x <= z => x <= y n z
            if right.label == n then {
              val a = right.args.head
              val b = right.args.tail.head
              var new_goal_1 = Sequent(goal.left, Set(left <= a))
              val s1 = prove(new_goal_1)
              if s1.isValid then {
                var new_goal_2 = Sequent(goal.left, Set(left <= b))
                val s2 = prove(new_goal_2)
                if s2.isValid then {
                  val s3 = have(goal) by Tautology.from(have(s1), have(s2), P6 of (x := left, y := a, z := b))
                  proven_sequent = proven_sequent + s3.judgement.asInstanceOf[proof.ValidProofTactic]
                  return s3.judgement
                }
              }
            }

            // Axioms P4'- P5' : x <= x u y, y <= x u y 
            if right.label == u then {
              val a = right.args.head
              val b = right.args.tail.head
              var new_goal_1 = Sequent(goal.left, Set(left <= a))
              val s1 = prove(new_goal_1)
              if s1.isValid then {
                val s3 = have(goal) by Tautology.from(have(s1), P4p of (x := a, y := b), transitivity of (x := left, y := a, z := right))
                proven_sequent = proven_sequent + s3.judgement.asInstanceOf[proof.ValidProofTactic]
                return s3.judgement
              }
              var new_goal_2 = Sequent(goal.left, Set(left <= b))
              val s2 = prove(new_goal_2)
              if s2.isValid then {
                val s3 = have(goal) by Tautology.from(have(s2), P5p of (x := a, y := b), transitivity of (x := left, y := b, z := right))
                proven_sequent = proven_sequent + s3.judgement.asInstanceOf[proof.ValidProofTactic]
                return s3.judgement
              }
            }

            // NC Axiom : x <= ne(x) => x <= y
            var new_goal_1 = Sequent(goal.left, Set(left <= Word_Problem.ne(left)))
            val s1 = prove(new_goal_1)
            if s1.isValid then {
              val s3 = have(goal) by Tautology.from(NC of (x := left, y := right), have(s1))
              proven_sequent = proven_sequent + s3.judgement.asInstanceOf[proof.ValidProofTactic]
              return s3.judgement
            }


            val current_relevant_term = extractRelevantTerm(goal)
            val useful_relevant_term = current_relevant_term.intersect(relevant_term)

            // Transitivity 
            for (elem <- useful_relevant_term) {
              if !(left == elem) && !(right == elem) then {
                var new_goal_1 = Sequent(goal.left, Set(elem <= right))
                val s1 = prove(new_goal_1)
                if s1.isValid then {
                  val new_goal_2 = Sequent(goal.left, Set(left <= elem)) 
                  val s2 = prove(new_goal_2)
                  if s2.isValid then {
                    val s3 = have(goal) by Tautology.from(have(s1), have(s2), transitivity of (x := left, y := elem, z := right))
                    proven_sequent = proven_sequent + s3.judgement.asInstanceOf[proof.ValidProofTactic]
                    return s3.judgement
                  }
                }
              }
            }
            return proof.InvalidProofTactic("The inequality is not true in general")
          }
        }
        goal.right.head match {
          case <=(left_t: Term, right_t: Term) => {
            return prove(goal)
          }

          // Equality in the conclusion
          case ===(left: Term, right: Term) => {
            var new_goal_1 = Sequent(goal.left, Set(left <= right))
            var s1 = prove(new_goal_1)
            if s1.isValid then {
              var new_goal_2 = Sequent(goal.left, Set(right <= left))
              var s2 = prove(new_goal_2)
              if s2.isValid then {
                val s3 = have(goal) by Tautology.from(have(s1), have(s2), antisymmetry of (x := left, y := right))
                return s3.judgement}
                else {return return proof.InvalidProofTactic("The equality is not true in general") }
            } else {return proof.InvalidProofTactic("The inequality is not true in general") }
          }

          case _ => return proof.InvalidProofTactic("Backward_Proof can only be applied to solve goals of the form (s1 <= t1, s2 <= t2, ..., sn <= tn) |- s <= t")
        }

      }
    }
  }



  val semiDistributivity = Theorem((x u (y n z)) <= ((x u y) n (x u z))) {
    have(thesis) by Backward_Proof.solve
  }

  val meetAssociative = Theorem((x n (y n z)) === ((x n y) n z)) {
    have(thesis) by Backward_Proof.solve
  }

  val idempotence = Theorem((x u x) === x) {
    have(thesis) by Backward_Proof.solve
  }

  val ExFalsoSequiturQuodlibet = Theorem((x n ne(x)) <= zero) {
    have(thesis) by Backward_Proof.solve
  }

  val TertiumNonDatur = Theorem(one <= (x u ne(x))) {
    have(thesis) by Backward_Proof.solve
  }

  val DeMorgan1 = Theorem((ne(x) n ne(y)) === ne(x u y)) {
    have(thesis) by Backward_Proof.solve
  }

  val DeMorgan2 = Theorem(ne(x n y)===(ne(x) u ne(y))) {
    have(thesis) by Backward_Proof.solve
  }

  val normalization = Theorem(((x n ne(w n ne(w))) u (y n (ne(z) u z))) === (y u (x n one))) {
    have(thesis) by Backward_Proof.solve
  }

  val transitivityTrain = Theorem((x <= y, y <=  z, z <= w, w <= t) |- x <= t ){
    have(thesis) by Backward_Proof.solve
  }

  val orthologicExample = Theorem(one <= (x n (ne(x) u y)) |- one <= y) {
    have(thesis) by Backward_Proof.solve
  }

  val doubleBound = Theorem((x <= ne(z), y <= ne(z)) |- ((x u y) n z) === zero) {
    have(thesis) by Backward_Proof.solve
  }

  
  val doubleFalse = Theorem((x n ne(x)) === (y n ne(y))) {
    have(thesis) by Backward_Proof.solve
  }

  val testOther = Theorem((x n z) === (x n z n ne(y n ne(x)))) {
    have(thesis) by Backward_Proof.solve
  }

  // interesting logic application
  // comment this theorem if there are memories issues  
  //val logicApplication = Theorem((one <= ((ne(x) u (ne(y) n z)) n (ne(ne(y) n z) u x)), ((ne(x) u (ne(y) n z)) n (ne(ne(y) n z) u x)) <= one,(x n (ne(ne(w)) u ne(z))) <= one, one <= (x n (ne(ne(w)) u ne(z))) ) |- ((ne(y) n w) === one)) {
  //  have(thesis) by Backward_Proof.solve
  //}
}
