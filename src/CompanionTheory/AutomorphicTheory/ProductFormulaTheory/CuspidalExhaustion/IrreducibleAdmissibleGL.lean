module

import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.IrreducibleAdmissibleGL
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.CuspEmbP
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExhUnipRadOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetOfInducedFiltrationStatement
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyExhaustion.PropsExh
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetSubLeftOfAdmissible
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.InducedCellSemisimplification
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IrreducibleSmoothAdmissibleGLStatement
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace CompanionTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem geometricLemmaGL : GlobalTheory.Published.GeometricLemma :=
  fun k _ _ _ _ => ⟨GlobalTheory.T.jacquet_of_induced_filtration k, _root_.GlobalTheory.CompanionTheory.Glob.cellSemisimplification k⟩

theorem embL_of_eq {x : IrrGL (k := k)} {l : List (IrrGL (k := k))} {y : Fin l.length → IrrGL (k := k)} (e : y = l.get)
    (hd : ∑ a, (y a).1 = x.1) (f : x.rep.IntertwiningMap (prodIrr y hd)) (hf : Function.Injective f) : EmbL x l := by
  subst e
  exact ⟨hd, f, hf⟩

theorem embL_pair {x : IrrGL (k := k)} {y : Fin 2 → IrrGL (k := k)} {hd : ∑ a, (y a).1 = x.1}
    {f : x.rep.IntertwiningMap (prodIrr y hd)} (hf : Function.Injective f) : EmbL x [y 0, y 1] :=
  embL_of_eq (l := [y 0, y 1]) (y := y) (funext fun i => by fin_cases i <;> rfl) hd f hf

theorem embL_nil (x : IrrGL (k := k)) (h0 : x.1 = 0) : EmbL x [] := by
  obtain ⟨n, c⟩ := x
  obtain rfl : n = 0 := h0
  have hd : ∑ a, (([] : List (IrrGL (k := k))).get a).1 = (⟨0, c⟩ : IrrGL (k := k)).1 := by simp
  obtain ⟨φ⟩ := exh_equiv_zero (stdBlocks (fun a => (([] : List (IrrGL (k := k))).get a).1) hd)
    (piTensor fun a => (([] : List (IrrGL (k := k))).get a).rep) (PiTensorProduct.isEmptyEquiv (Fin 0)) c.rep.ρ c.rep.irr
  exact ⟨hd, φ.symm.toIntertwiningMap, fun v w h => φ.symm.toLinearEquiv.injective h⟩


variable (k) in
theorem cuspEmbP (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hR : RefineP k) : CuspEmbP k := by
  apply _root_.PositivityTheory.Exh.cuspEmbP_of_refine <;> assumption


variable (k) in
theorem suppP : SuppP k := by
  intros
  apply _root_.PositivityTheory.Exh.suppP <;> assumption

theorem irreducibleAdmissibleGL : GlobalTheory.Published.IrreducibleAdmissibleGL :=
  fun k _ _ _ _ n => GlobalTheory.T.irreducible_smooth_admissible_GL k (Fin n)


variable (k) in
theorem cuspEmbP_of_refine (hR : RefineP k) : CuspEmbP k :=
  cuspEmbP k irreducibleAdmissibleGL hR

end CompanionTheory.Exh

end
