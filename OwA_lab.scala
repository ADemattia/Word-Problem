//> using scala "3.5.1"
//> using dep "ch.epfl.lara::lisa::0.7,url=https://github.com/epfl-lara/lisa/releases/download/0.7/lisa_3-0.7.jar"

import lisa.automation.Substitution.ApplyRules as Substitution
import lisa.automation.Tableau
import scala.util.Try

object OwA_lab extends lisa.Main {

  val x = variable
  val y = variable
  val z = variable
  val zero = ConstantTermLabel("zero", 0)
  addSymbol(zero)

  var one = ConstantTermLabel("one", 0)
  addSymbol(one)

  // We introduce the signature of lattices
  val <= = ConstantPredicateLabel.infix("<=", 2)
  addSymbol(<=)
  val u = ConstantFunctionLabel.infix("u", 2) // join (union for sets, disjunction in boolean algebras)
  addSymbol(u)
  val n = ConstantFunctionLabel.infix("n", 2) // meet (interestion for sets, conjunction in boolean algebras)
  addSymbol(n)
  val ne = ConstantFunctionLabel("ne", 1)
  addSymbol(ne)

  // Enables infix notation
  extension (left: Term) {
    def <=(right: Term): Formula = (OwA_lab.<= : ConstantPredicateLabel[2])(left, right)
    infix def u(right: Term): Term = (OwA_lab.u: ConstantFunctionLabel[2])(left, right)
    infix def n(right: Term): Term = (OwA_lab.n: ConstantFunctionLabel[2])(left, right)
    def ne: Term = (OwA_lab.ne: ConstantFunctionLabel[1])(left)
    def zero: Term = (OwA_lab.zero)
    def one: Term = (OwA_lab.one)
  }
  // We will now prove some statement about partial orders, which we axiomatize
  val reflexivity = Axiom(x <= x)
  val antisymmetry = Axiom(((x <= y) /\ (y <= x)) ==> (x === y))
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
  // da eliminare
  val P9 = Axiom((x n ne(x)) <= zero)
  val P9p = Axiom(one <= (x u ne(x)))
  val P3 = Axiom(zero <= x)
  val P3p = Axiom(x <= one)
  val noz = Axiom(ne(one) <= zero)
  val onz = Axiom(one <= ne(zero))

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

  // Now we'll need to reason with equality. We can do so with the Substitution tactic, which substitutes equals for equals.
  // The argument of Substitutions can be either an equality (s===t). In this case, the result should contain (s===t) in assumptions.
  // Or it can be a previously proven step showing a formula of the form (s===t).
  // In this case, assumptions of this precedently proven fact need to be in the assumptions of the conclusion.

  // Note however that Restate and Tautology now by themselves that t === t, for any t.

  // Tedious, isn't it
  // Can we automate this?
  // Yes, we can!

  import lisa.prooflib.ProofTacticLib.ProofTactic
  import lisa.prooflib.Library

  object OwA extends ProofTactic {
    def solve(using lib: library.type, proof: lib.Proof)(goal: Sequent): proof.ProofTacticJudgement = {
      if goal.right.size != 1 then proof.InvalidProofTactic("OwA can only be applied to solve goals of the form (s1 <= t1, s2 <= t2, ..., sn <= tn) |- s <= t")
      else{ // Starting the proof of goal

        def Extract_known_term(goal: Sequent): Set[OwA_lab.Term] = {
          val axiom_set = goal.left
          val toprove = goal.right
          var total_set = goal.left ++ goal.right
          var total_term_set : Set[OwA_lab.Term] = Set() 
          for (elem <- total_set) {
            elem match {
              case <=(left: OwA_lab.Term, right: OwA_lab.Term) =>{
                total_term_set += left
                total_term_set += right}
              case _ =>
            }
          }

          def subExtract(set: Set[OwA_lab.Term]): Set[OwA_lab.Term] = {
            var final_set = set
            for (elem <- set) {
              if elem.label == OwA_lab.ne then {
                val a = elem.args.head
                final_set = final_set + a  
              }
              if elem.label == OwA_lab.n then {
                val a = elem.args.head
                val b = elem.args.tail.head
                final_set = final_set + a
                final_set = final_set + b

              }
              if elem.label == OwA_lab.u then {
                val a = elem.args.head
                val b = elem.args.tail.head
                final_set = final_set + a
                final_set = final_set + b
              }
            }

            if final_set == set then { // nothing more was extracted
              return final_set
            }
              return subExtract(final_set)
          }

          def Complementation(set2: Set[OwA_lab.Term]): Set[OwA_lab.Term] = {
            var complementation = set2
            for (elem <- set2) {
              complementation = complementation + (OwA_lab.ne(elem))
              complementation = complementation + (OwA_lab.ne(OwA_lab.ne((elem))))
            }
            return complementation 
          }

          val known_term = subExtract(total_term_set)
          return Complementation(known_term)
        }

        val axiom_set = goal.left
        var axiom_term: Set[Term] = Set()
        for (elem <- axiom_set) {
          elem match {
            case <=(left: Term, right: Term) =>{
              axiom_term += left
              axiom_term += right
          }
          case _=> 
        }
       }
        val known_term = Extract_known_term(goal)
        println(known_term.size)
        var i = 0
        val debug = 0
        var proven_sequent: Set[proof.ValidProofTactic] = Set()
        var visited_sequent: Set[Sequent] = Set()

        def prove(goal: Sequent): proof.ProofTacticJudgement = {
          for (elem <- proven_sequent) {
            if elem.bot == goal then {
              val s1 = have(goal) by Tautology.from(have(elem))
              return s1.judgement
            }
            
          }

          if visited_sequent.contains(goal) then {
              if debug == 1 then {
              println(s"gia visitato e non provato il seguente ${i}")
              println(goal.right.head)
              i += 1   
              println("-------------------")}
              return proof.InvalidProofTactic("The inequality is not true in general")}
          else {
            visited_sequent += (goal)
            if axiom_set.contains(goal.right.head) then {
              if debug == 1 then {
              println(s"in assiomi ${i}")
              i += 1
              println(goal.right.head)
              println("-------------------")}
              val s1 = have(goal) by Restate
              proven_sequent = proven_sequent + s1.judgement.asInstanceOf[proof.ValidProofTactic]
              return s1.judgement
            } else {
              goal.right.head match {
                case <=(left: Term, right: Term) => {
                  // REFLEXIVITY
                  if left == right then {
                    if debug == 1 then {
                    println(s"riflessivita ${i}")
                    i += 1
                    println(goal.right.head)
                    println("-------------------")}
                    val s1 = have(goal) by Tautology.from(reflexivity of (x := left))
                    proven_sequent = proven_sequent + s1.judgement.asInstanceOf[proof.ValidProofTactic]
                    return s1.judgement
                  }

                  if right == OwA_lab.ne(OwA_lab.ne(left)) then {
                    if debug == 1 then {
                    println(s"assioma P7 ${i}")
                    i += 1
                    println(goal.right.head)
                    println("-------------------")}
                    val s1 = have(goal) by Tautology.from(P7 of (x := left))
                    proven_sequent = proven_sequent + s1.judgement.asInstanceOf[proof.ValidProofTactic]
                    return s1.judgement
                  }
                  if left == OwA_lab.ne(OwA_lab.ne(right)) then {
                    if debug == 1 then {
                    println(s"assioma P7p ${i}")
                    i += 1
                    println(goal.right.head)
                    println("-------------------")}
                    val s1 = have(goal) by Tautology.from(P7p of (x := right))
                    proven_sequent = proven_sequent + s1.judgement.asInstanceOf[proof.ValidProofTactic]
                    return s1.judgement
                  }

                  if (left.label == OwA_lab.ne && left.args == Seq(one)) & right == zero then {
                    if debug == 1 then {
                    println(s"noz ${i}")
                    i += 1
                    println(goal.right.head)
                    println("-------------------")}
                    val s1 = have(goal) by Tautology.from(noz)
                    proven_sequent = proven_sequent + s1.judgement.asInstanceOf[proof.ValidProofTactic]
                    return s1.judgement
                  }

                  if left == one & (right.label == OwA_lab.ne && right.args == Seq(zero)) then {
                    if debug == 1 then {
                    println(s"onz ${i}")
                    i += 1
                    println(goal.right.head)
                    println("-------------------")}
                    val s1 = have(goal) by Tautology.from(onz)
                    proven_sequent = proven_sequent + s1.judgement.asInstanceOf[proof.ValidProofTactic]
                    return s1.judgement
                  }

                  // P3 & P3'
                  if left == zero then {
                    if debug == 1 then {
                    println(s"zero <= x ${i}")
                    i += 1
                    println(goal.right.head)
                    println("-------------------")}
                    val s1 = have(goal) by Tautology.from(P3 of (x := right))
                    proven_sequent = proven_sequent + s1.judgement.asInstanceOf[proof.ValidProofTactic]
                    return s1.judgement
                  }
                  if right == one then {
                    if debug == 1 then {
                    println(s"x <= one ${i}")
                    i += 1
                    println(goal.right.head)
                    println("-------------------")}
                    val s1 = have(goal) by Tautology.from(P3p of (x := left))
                    proven_sequent = proven_sequent + s1.judgement.asInstanceOf[proof.ValidProofTactic]
                    return s1.judgement
                  }

                  // P9 & P9'
                  left.args match {
                    case Seq(a, OwA_lab.ne(b)) =>
                      if left.label == n && a == b && right == zero then {
                        if debug == 1 then {
                        println(s"P9 ${i}")
                        i += 1
                        println(goal.right.head)
                        println("-------------------")}
                        val s1 = have(goal) by Tautology.from(P9 of (x := a))
                        proven_sequent = proven_sequent + s1.judgement.asInstanceOf[proof.ValidProofTactic]
                        return s1.judgement
                      }
                    case _ =>
                  }
                  right.args match {
                    case Seq(a, OwA_lab.ne(b)) =>
                      if right.label == u && a == b && left == one then {
                        if debug == 1 then {
                        println(s"P9' ${i}")
                        i += 1
                        println(goal.right.head)
                        println("-------------------")}
                        val s1 = have(goal) by Tautology.from(P9p of (x := a))
                        proven_sequent = proven_sequent + s1.judgement.asInstanceOf[proof.ValidProofTactic]
                        return s1.judgement
                      }
                    case _ =>
                  }

                  // P8
                  if left.label == OwA_lab.ne && right.label == OwA_lab.ne then {
                    if debug == 1 then {
                    println(s"ne(y) <= ne(x) ${i}")
                    i += 1
                    println(goal.right.head)
                    println("-------------------")}
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

                  if left.label == OwA_lab.n then {
                    if debug == 1 then {
                    println(s"left n ${i}")
                    i += 1
                    println(goal.right.head)
                    println("-------------------")}
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

                  if left.label == OwA_lab.u then {
                    if debug == 1 then {
                    println(s"left u ${i}")
                    i += 1
                    println(goal.right.head)
                    println("-------------------")}
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

                  if right.label == OwA_lab.n then {
                    if debug == 1 then {
                    println(s"Right n ${i}")
                    i += 1
                    println(goal.right.head)
                    println("-------------------")}
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

                  if right.label == OwA_lab.u then {
                    if debug == 1 then {
                    println(s"Right u ${i}")
                    i += 1
                    println(goal.right.head)
                    println("-------------------")}
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
                  val current_known_term = Extract_known_term(goal)
                  val useful_known_term = current_known_term.intersect(known_term)
                  for (elem <- useful_known_term) {
                    if !(left == elem) && !(right == elem) then {
                      if debug == 1 then {
                      println(s"Assiomi Transitivita ${i}")
                      i += 1
                      println(goal.right.head)
                      println("Termine di taglio")
                      println(elem)
                      println("-------------------") }
                      var new_goal_1 = Sequent(goal.left, Set(elem <= right))
                      val s1 = prove(new_goal_1)
                      if s1.isValid then {
                        var new_goal_2 = Sequent(goal.left, Set(left <= elem))
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

                case _ => {
                  return proof.InvalidProofTactic("The inequality is not true in general")
                }
              }
            }
          }
        }
        return prove(goal)
      }
    }
  }

  val DeMorgan1 = Theorem((ne(x) n ne(y)) <= ne(x u y)) {
    have(thesis) by OwA.solve
  }
  val DeMorgan2 = Theorem(ne(x u y) <= (ne(x) n ne(y))) {
    have(thesis) by OwA.solve
  }
  val DeMorgan3 = Theorem((ne(x) u ne(y)) <= ne(x n y) ) {
    have(thesis) by OwA.solve
  }
  val DeMorgan4 = Theorem(ne(x n y) <= (ne(x) u ne(y))) {
    have(thesis) by OwA.solve
  }
 // val test2 = Theorem(x <= ne(ne(x))) {
  //  have(thesis) by OwA.solve
  //}
  val EXTOA= Theorem(one <= (x n (ne(x) u y)) |- one <= y) {
   have(thesis) by OwA.solve
  }

  val test1 = Theorem(x <= x) {
    have(thesis) by OwA.solve
  }
  val test2 = Theorem(x <= (x u y)) {
    have(thesis) by OwA.solve
  }
  val test3 = Theorem((y n x) <= x) {
    have(thesis) by OwA.solve
  }
  val test4 = Theorem((x n y) <= (y u z)) {
    have(thesis) by OwA.solve
  }
  val semiDistributivity = Theorem((x u (y n z)) <= ((x u y) n (x u z))) {
    have(thesis) by OwA.solve
  }



}
