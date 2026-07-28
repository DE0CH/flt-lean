import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.FieldTheory.Finite.Basic

open IsDedekindDomain

example (F : Type) [Field F] [NumberField F]
    (w : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (hw2 : (2 : NumberField.RingOfIntegers F) ∉ w.asIdeal) : True := by
  haveI : w.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal w.isPrime w.ne_bot
  haveI : Finite (NumberField.RingOfIntegers F ⧸ w.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  haveI : Fintype (NumberField.RingOfIntegers F ⧸ w.asIdeal) := Fintype.ofFinite _
  letI : Field (NumberField.RingOfIntegers F ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
  obtain ⟨p, hp⟩ := CharP.exists (NumberField.RingOfIntegers F ⧸ w.asIdeal)
  haveI := hp
  obtain ⟨n, hprime, hcard'⟩ := FiniteField.card (K := NumberField.RingOfIntegers F ⧸ w.asIdeal) p
  trivial
