module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CardStabilizerForgetFr
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle137
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle136
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitOfConjPNe
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle053
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmThetaTranslatesPrimeToQIntegral
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicPeriodicContinuousEqZeroOfFourierCoeff
public import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle326
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle142
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle064
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle085
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle086
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

@[expose] public section

section


theorem _root_.GlobalTheory.T.cm_localDensities_productFormula : GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.DensityProduct := by
  first | exact @GlobalTheory.Proof.cm_localDensities_productFormula.densityProduct | exact GlobalTheory.Proof.cm_localDensities_productFormula.densityProduct | (intros; apply GlobalTheory.Proof.cm_localDensities_productFormula.densityProduct <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.PeriodOnStep

open NumberField IsDedekindDomain Module Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.DivisionValues
open GlobalTheory.IndefiniteRowSideFullHecke
open GlobalTheory.PeriodClassSum GlobalTheory.Mem.Col2
open scoped Matrix ComplexOrder

section Step

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs)

theorem Lsh_eq_N {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}
    (d : DecoSet (E := E) (n := n) (ST := ∅) (SG := SG)) : d.1.Lsh = d.1.N := by
  have e : d.1.L = d.1.N := by
    rw [Deco.L]
    simp
  rw [Deco.Lsh, e]
  exact d.2.uni

theorem emb_mem_cmMax (hX : X.Ok) (τ : X.Tau) (x : X.E) : X.emb τ x ∈ cmMax X.K := fun φ => by
  rw [← hX.emb_star]
  exact hX.conjE (φ.comp (X.emb τ)) x

theorem root_mem_cmMax (hX : X.Ok) {c : X.K} (hc : ∃ m : ℕ, 0 < m ∧ c ^ m = 1) : c ∈ cmMax X.K := fun φ => by
  obtain ⟨m, hm, hc⟩ := hc
  have h1 := star_mul_root hX.conjK hm hc
  have h2 : star (φ c) * φ c = 1 := by
    have h3 : ‖φ c‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hc, map_one]) hm.ne'
    rw [← starRingEnd_apply, Complex.conj_mul', h3]
    simp
  have h0 : φ c ≠ 0 := right_ne_zero_of_mul_eq_one h2
  refine mul_right_cancel₀ h0 ?_
  rw [← map_mul, h1, map_one, starRingEnd_apply, h2]

theorem row_act_rat (hX : X.Ok) (g : (mtildeGSD W Ch sel mu P).G) (i j) :
    (mtildeGSD W Ch sel mu P).bV.repr ((mtildeGSD W Ch sel mu P).ρ g ((mtildeGSD W Ch sel mu P).bV j)) i ∈ cmMax X.K := by
  rw [formGSD_rho, map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact mul_mem (root_mem_cmMax hX (LevFam.chr_root _ _))
    (coefAction_repr_mem_subfield X.emb _ W.sgTrue (emb_mem_cmMax hX) _ i j).1

theorem isFormsOf_MtildeH (hX : X.Ok) : IsFormsOf _ (mtildeOk W Ch sel mu hX P) (MtildeL W Ch sel mu P)
    (MtildeH W Ch hX sel mu P) (LinearEquiv.refl _ _) :=
  isFormsOf_toH _ _ (row_act_rat W Ch sel mu P hX) (fun v => by rw [row_gramV]; exact gramB_posDef _ _) _

def rowPt (c : (stepX Ch sel mu P).Cl) : RowPt Pr R sel mu := toRow sel mu ((stepX Ch sel mu P).rep c).1.1

def rowCl (c : (stepX Ch sel mu P).Cl) : (mtildeGSD W Ch sel mu P).Cl := (mtildeGSD W Ch sel mu P).cls (rowPt Ch sel mu P c)

theorem rowCl_surjective : Function.Surjective (rowCl W Ch sel mu P) := by
  rintro ⟨d⟩
  obtain ⟨p, rfl⟩ := toRow_surjective sel mu d
  refine ⟨(stepX Ch sel mu P).cl () (trivPt X _ _ _ _ p), ?_⟩
  obtain ⟨g, hg⟩ := (stepX Ch sel mu P).exists_mv () (trivPt X _ _ _ _ p)
  have h1 := congrArg (fun q => toRow sel mu q.1.1) hg
  refine Eq.symm (((mtildeGSD W Ch sel mu P).cls_eq_iff _ _).2 ⟨toRowG Ch sel mu P g, ?_⟩)
  exact (toRow_smul Ch sel mu P g _).symm.trans h1

variable (hd : Disjoint Pr.vGs (QE sel (mu : Chr X.F X.E X.K)))


include hd in
theorem exists_step_smul (a : FormG (rowTy Ch sel mu P).inv) (p q : (stepX Ch sel mu P).D ())
    (h : a • toRow sel mu p.1.1 = toRow sel mu q.1.1) :
    ∃ g : (stepX Ch sel mu P).G (), toRowG Ch sel mu P g = a ∧ (letI := (stepX Ch sel mu P).actD (); g • p) = q := by
  obtain ⟨g, h1, h2⟩ := exists_toRowG_smul Ch sel mu P hd a _ _ h
  refine ⟨g, h1, (trivPt X _ _ _ _).symm.injective h2⟩

include hd in
theorem rowCl_injective : Function.Injective (rowCl W Ch sel mu P) := by
  rintro ⟨⟨⟩, c⟩ ⟨⟨⟩, c'⟩ h
  obtain ⟨a, ha⟩ := ((mtildeGSD W Ch sel mu P).cls_eq_iff _ _).1 h
  obtain ⟨g, -, hg⟩ := exists_step_smul Ch sel mu P hd a _ _ ha
  refine congrArg (Sigma.mk ()) ?_
  rw [← (stepX Ch sel mu P).rp_spec () c, ← (stepX Ch sel mu P).rp_spec () c']
  exact Quotient.sound ⟨g, hg⟩

def clEquiv : (stepX Ch sel mu P).Cl ≃ (mtildeGSD W Ch sel mu P).Cl :=
  Equiv.ofBijective _ ⟨rowCl_injective W Ch sel mu P hd, rowCl_surjective W Ch sel mu P⟩


include hd in
theorem card_stab (c : (stepX Ch sel mu P).Cl) : Nat.card ((stepX Ch sel mu P).Stab c) =
    Nat.card (MulAction.stabilizer (mtildeGSD W Ch sel mu P).G (rowPt Ch sel mu P c)) := by
  refine Eq.trans ?_ (card_stabilizer_toRow Ch sel mu P hd _)
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun g => ?_)
  exact (trivPt X _ _ _ _).symm.injective.eq_iff.symm


variable (hF : ((stepX Ch sel mu P).fam X.emb W.sgTrue).Ok)

end Step

section Lattice

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (hd : Disjoint Pr.vGs (QE sel (mu : Chr X.F X.E X.K)))
  (hF : ((stepX Ch sel mu P).fam X.emb W.sgTrue).Ok) (h' : (dualGSD W Ch sel mu P).Ok)

end Lattice

section Pol

variable {K : Type} [Field K] (σ : K →+* ℂ)

theorem map_fockB {τ : Type} (f g : MvPolynomial τ K) : σ (fockB f g) = fockB (MvPolynomial.map σ f) (MvPolynomial.map σ g) := by

  rw [fockB_eq_sum _ _ f.support (MvPolynomial.support_map_subset _ _), fockB, map_sum]
  exact Finset.sum_congr rfl fun m _ => by rw [map_mul, map_mul, map_natCast, MvPolynomial.coeff_map, MvPolynomial.coeff_map]

theorem map_pairB {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (F F' : Pol K ι n) :
    σ (pairB lam F F') = pairB lam (MvPolynomial.map σ F) (MvPolynomial.map σ F') := by
  rw [pairB_apply, pairB_apply, map_mul, map_inv₀, map_fockB, extNormB, extNormB, map_prod]
  congr 2
  exact Finset.prod_congr rfl fun τ _ => by rw [map_fockB, Formalism.L2.DIV.map_extremal]

theorem polOf_evV {E ι : Type} [Field E] [Fintype ι] {n : ℕ} (emb : ι → E →+* K) (lam : ι → DomWeight n) (x : VV K lam) :
    polOf (Gr emb σ n) (Formalism.L2.Forms.shiftOf lam) (fr0 emb σ n) (evV emb 1 lam σ x) = MvPolynomial.map σ x.1 := by
  have e : (fun τ => ((fr0 emb σ n).1 τ)⁻¹) = 1 := funext fun _ => inv_one
  rw [evV_apply, ← e, polOf_fnOf]

end Pol

section Layer

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) {I : ChainIn X.E X.K X.Tau R} (b0 : (I.S R.m).β)
  (til : ∀ b, (stepX Ch sel mu P).D b → (I.S R.m).D b0) (ext : ∀ b, (stepX Ch sel mu P).G b →* (I.S R.m).G b0)
  (tz : X.E) (H : ∀ b, Subgroup ((stepX Ch sel mu P).G b))

@[reducible] def perOn : PerIn I where
  S' := stepX Ch sel mu P
  b0 := b0
  til := til
  ext := ext
  sg := W.sgW
  tz := tz
  H := H

variable (hd : Disjoint Pr.vGs (QE sel (mu : Chr X.F X.E X.K))) (σ : X.K →+* ℂ)


include hd in
theorem row_law (z : (mtildeGSD W Ch sel mu P).EqFun) (g : (stepX Ch sel mu P).G ()) (d : (stepX Ch sel mu P).D ()) :
    MvPolynomial.map σ (z.1 (toRow sel mu (letI := (stepX Ch sel mu P).actD (); g • d : (stepX Ch sel mu P).D ()).1.1)).1 =
      (σ ((stepX Ch sel mu P).chr () g : X.K))⁻¹ • rhoP W.sgTrue (embGL (embAt σ X.emb) ((stepX Ch sel mu P).gam () g))
        (MvPolynomial.map σ (z.1 (toRow sel mu d.1.1)).1) := by
  have h1 := z.2 (toRowG Ch sel mu P g) (toRow sel mu d.1.1)
  rw [mtilde_rho_toRowG W Ch sel mu P hd] at h1
  have h2 := (congrArg z.1 (toRow_smul Ch sel mu P g d.1.1)).trans h1
  refine (congrArg (fun y : VV X.K W.sgTrue => mapS σ y.1) h2).trans ?_
  refine (LinearMap.map_smulₛₗ (mapS σ) _ (actP W.sgTrue (embGL X.emb (ufGL _ _ g.1)) (z.1 (toRow sel mu d.1.1)).1)).trans ?_
  rw [Units.val_inv_eq_inv_val, map_inv₀, mapS_apply, GlobalTheory.ValCmp.use₂]
  congr 1

def rowEmb : (mtildeGSD W Ch sel mu P).EqFun →ₛₗ[σ] (perOn W Ch sel mu P b0 til ext tz H).Mt X.emb σ where
  toFun z := ⟨fun _ d => MvPolynomial.map σ (z.1 (toRow sel mu d.1.1)).1, fun _ d =>
    ⟨GlobalTheory.Proof.TensorMapDescent.map_mem_VV σ W.sgTrue _ (z.1 (toRow sel mu d.1.1)).2, fun g _ => row_law W Ch sel mu P hd σ z g d⟩⟩
  map_add' _ _ := Subtype.ext (funext fun _ => funext fun _ => map_add (mapS σ) _ _)
  map_smul' _ _ := Subtype.ext (funext fun _ => funext fun _ => LinearMap.map_smulₛₗ (mapS σ) _ _)

variable (hX : X.Ok) (hc : X.Tau → HCParam R)
  {Pl : Rows.Places X.K} (J : AtIn I) (Z : FmIn J Pl) (hI : I.Ok) (hJ : J.Ok)
  (hQ : (perOn W Ch sel mu P b0 til ext tz H).Ok) (l : J.Laws X.emb σ hc)
  (lf : FmLaws J (perOn W Ch sel mu P b0 til ext tz H) X.emb σ hc Pl hI hQ)
  (hT : (perOn W Ch sel mu P b0 til ext tz H).Over J)

section AnyLattice

variable {Λ' : HLat X.K} {ι : Λ'.V ≃ₗ[X.K] (mtildeGSD W Ch sel mu P).EqFun}
  (hι : IsFormsOf _ (mtildeOk W Ch sel mu hX P) (MtildeL W Ch sel mu P) Λ' ι)

include hι

end AnyLattice

end Layer

end GlobalTheory.PeriodOnStep
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

theorem _root_.GlobalTheory.T.mem_locW_hlat_iff' : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] (emb : ι → E →+* K) (Pl : Rows.Places K) (pw : Pl.Pl → HeightOneSpectrum (𝓞 K)), (∀ w (x : K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ)) → ∀ {n : ℕ} (S : GStep E K n) (lam : ι → DomWeight n) (h : (S.fam emb lam).Ok), S.Ok → ∀ (w : Pl.Pl) (x : (S.hlat emb lam h).V), x ∈ locW Pl w (S.hlat emb lam h).L ↔ ∀ c, x.1 c ∈ locW Pl w (delAtr emb lam (S.Lsh c.1 (S.rep c))) := by
  first | exact @GlobalTheory.Mem.Col2.mem_locW_hlat_iff | exact GlobalTheory.Mem.Col2.mem_locW_hlat_iff | (intros; apply GlobalTheory.Mem.Col2.mem_locW_hlat_iff <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.DetIdlValue

variable {X : Fields} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}

theorem finprod_group {M : Type} [CommMonoid M] (hX : X.Ok) (hsel : IsSel X sel) (g : HeightOneSpectrum (𝓞 X.E) → M)
    (hfin : (Function.mulSupport g).Finite) (h1 : ∀ w, conjPrime₂ w = w → g w = 1) :
    ∏ᶠ w, g w = ∏ᶠ v, g (sel v) * g (conjPrime₂ (sel v)) := by
  classical
  have hu : ∀ v, (sel v).under (𝓞 X.F) = v := fun v => HeightOneSpectrum.ext (hsel v)
  have hu' : ∀ v, (conjPrime₂ (sel v)).under (𝓞 X.F) = v := fun v =>
    HeightOneSpectrum.ext ((GlobalTheory.MuOffMove.under_conjP hX _).trans (hsel v))
  have hsub : Function.mulSupport (fun v => g (sel v) * g (conjPrime₂ (sel v))) ⊆
      (hfin.toFinset.image fun P => P.under (𝓞 X.F) : Finset _) := by
    intro v hv
    rw [Finset.mem_coe, Finset.mem_image]
    by_cases h : g (sel v) = 1
    · refine ⟨conjPrime₂ (sel v), hfin.mem_toFinset.2 fun h' => hv ?_, hu' v⟩
      simp only [h, h', mul_one]
    · exact ⟨sel v, hfin.mem_toFinset.2 h, hu v⟩
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub, finprod_eq_prod _ hfin,
    ← Finset.prod_fiberwise_of_maps_to (g := fun P : HeightOneSpectrum (𝓞 X.E) => P.under (𝓞 X.F))
      fun P hP => Finset.mem_image_of_mem (fun P : HeightOneSpectrum (𝓞 X.E) => P.under (𝓞 X.F)) hP]
  refine Finset.prod_congr rfl fun v _ => ?_
  by_cases hc : conjPrime₂ (sel v) = sel v
  · rw [hc, h1 _ hc, mul_one]
    refine Finset.prod_eq_one fun w hw => h1 w ?_
    by_contra hw'
    have hwv : w.asIdeal.under (𝓞 X.F) = v.asIdeal := congrArg HeightOneSpectrum.asIdeal (Finset.mem_filter.1 hw).2
    rcases ((GlobalTheory.ThetaMove.split_of_conj_ne₂ X w v hX hw' hwv).2 (sel v)).1 (hsel v) with e | e
    · exact hw' (e ▸ hc)
    · rw [e, GlobalTheory.CharValCompare.conjP_conjP] at hc
      exact hw' hc.symm
  · have hsp := (GlobalTheory.ThetaMove.split_of_conj_ne₂ X (sel v) v hX hc (hsel v)).2
    rw [← Finset.prod_pair (Ne.symm hc)]
    refine Finset.prod_subset (fun w hw => ?_) fun w hw hw' => ?_
    · rw [Finset.mem_insert, Finset.mem_singleton]
      exact (hsp w).1 (congrArg HeightOneSpectrum.asIdeal (Finset.mem_filter.1 hw).2)
    · by_contra hg
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      exact hw' (Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 hg, HeightOneSpectrum.ext ((hsp w).2 hw)⟩)

theorem pow_toNat_mul {G : Type} [CommGroup G] (a : G) (k : ℤ) : a ^ k.toNat * a⁻¹ ^ (-k).toNat = a ^ k := by
  rw [inv_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_sub, Int.toNat_sub_toNat_neg]

private theorem span_eq_top_of_isSdLat {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {N : Submodule (𝓞 E) (Sp E n)} (hN : IsSdLat N) :
    Submodule.span E (N : Set (Sp E n)) = ⊤ := by
  classical
  apply Submodule.dualAnnihilator_eq_bot_iff.mp
  apply le_antisymm ?_ bot_le
  intro f hf
  let v : Sp E n := fun i => star (f (Pi.single i 1))
  have hpair : hStd E n v = f := by
    apply (Pi.basisFun E (Fin n)).ext
    intro i
    rw [Pi.basisFun_apply, hStd_apply, Finset.sum_eq_single i]
    · simp [v]
    · intro j _ hj
      simp [hj]
    · simp
  have hline (r : E) : r • v ∈ N := by
    rw [← show dual (hStd E n) N = N from hN.2, dualBasic_mem_dual]
    intro y hy
    have hy0 : hStd E n v y = 0 := by
      rw [hpair]
      exact (Submodule.mem_dualAnnihilator f).mp hf y (Submodule.subset_span hy)
    have hz : hStd E n y v = 0 := by
      simpa [hy0] using ((hStd_isSymm (E := E) (n := n)).eq v y).symm
    simp [hz]
  have hv : v = 0 := by
    funext i
    change v i = 0
    by_contra hi
    let coord := (LinearMap.proj i : Sp E n →ₗ[E] E).restrictScalars (𝓞 E)
    have htop : N.map coord = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact ⟨(x / v i) • v, hline _, div_mul_cancel₀ _ hi⟩
    have : Module.Finite (𝓞 E) E := Module.finite_def.mpr (htop ▸ hN.1.fg.map coord)
    exact RingOfIntegers.not_isField E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
  rw [Submodule.mem_bot]
  simpa [hv] using hpair.symm


theorem ordSub_eq_ordDet {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {N : Submodule (𝓞 E) (Sp E n)}
    (hN : IsSdLat N) (w : HeightOneSpectrum (𝓞 E)) : GlobalTheory.Mem.Chr.ordSub w (GlobalTheory.Mem.Chr.detSub N) = ordDet w N := by
  letI : Submodule.IsLattice E N := hN.1
  have hfull : Submodule.IsFullLattice E N := ⟨span_eq_top_of_isSdLat hN⟩
  apply ordSub_detSub_eq hfull
  apply GlobalTheory.CharValCompare.isFr_frameAt
  first
  | exact GlobalTheory.CharValCompare.exists_isFr w hN
  | exact GlobalTheory.CharValCompare.exists_isFr w hN.1

theorem inv_val_detIdl : ∀ (X : Fields) (n : ℕ) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (SB : Finset (HeightOneSpectrum (𝓞 X.E))) (χ : Formalism.L2.Host.HChar X.E) (σ : X.K →+* ℂ) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (N : Submodule (𝓞 X.E) (Sp X.E n)) (fr : HeightOneSpectrum (𝓞 X.E) → Sp X.E n ≃ₗ[X.E] Sp X.E n), X.Ok → IsSel X sel → IsSdLat N → χ.TrivOn X.F → (∀ w, w ∉ SB → conjPrime₂ w ∉ SB → χ.UnrAt w ∧ σ ((mU w : X.Kˣ) : X.K) = ((χ.val w : ℂˣ) : ℂ)⁻¹) → ((χ.1 (detIdl SB N fr) : ℂˣ) : ℂ)⁻¹ = σ (muOff sel SB mU N) * ∏ P : SB, ((χ.locK P.1 (LinearEquiv.det (fr P.1)) : ℂˣ) : ℂ)⁻¹ := by
  intro X n sel SB χ σ mU N fr hX hsel hN hT hU
  classical
  set g : HeightOneSpectrum (𝓞 X.E) → ℂˣ := fun w =>
    if w ∈ SB ∨ conjPrime₂ w ∈ SB then 1 else χ.val w ^ (ordDet w N).toNat with hg
  have hfin : (Function.mulSupport g).Finite := by
    refine (GlobalTheory.OrdDetConj.ordDet_conj_finite X.E n N hN).2.subset fun w hw h0 => hw ?_
    simp [hg, h0]
  have h0 : ∀ w, conjPrime₂ w = w → ordDet w N = 0 := fun w hw => by
    have := GlobalTheory.OrdDetConj.ordDet_conjP hN w
    rw [hw] at this
    omega
  have h1 : ∀ w, conjPrime₂ w = w → g w = 1 := fun w hw => by simp [hg, h0 w hw]
  have e1 : χ.1 (detIdl SB N fr) = (∏ P ∈ SB, χ.locK P (LinearEquiv.det (fr P))) * ∏ᶠ w, g w := by
    unfold detIdl
    rw [map_mul, map_prod, MonoidHom.map_finprod _ (finite_detIdl SB hN.1)]
    congr 1
    refine finprod_congr fun w => ?_
    simp only [hg]
    split_ifs
    · exact map_one _
    · rw [map_pow, ordSub_eq_ordDet hN]
      rfl
  have e2 : ∀ v, σ (GlobalTheory.MuOffMove.term sel SB mU N v) = (((g (sel v) * g (conjPrime₂ (sel v)))⁻¹ : ℂˣ) : ℂ) := by
    intro v
    unfold GlobalTheory.MuOffMove.term
    by_cases hc : conjPrime₂ (sel v) = sel v
    · rw [hc, h1 _ hc, h0 _ hc]
      simp
    · obtain ⟨hm, hsp⟩ := GlobalTheory.ThetaMove.split_of_conj_ne₂ X (sel v) v hX hc (hsel v)
      by_cases hv : sel v ∈ SB ∨ conjPrime₂ (sel v) ∈ SB
      · have hv' : ∃ P ∈ SB, P.asIdeal.under (𝓞 X.F) = v.asIdeal :=
          hv.elim (fun h => ⟨_, h, (hsp _).2 (Or.inl rfl)⟩) fun h => ⟨_, h, (hsp _).2 (Or.inr rfl)⟩
        rw [if_pos hv']
        simp only [hg, GlobalTheory.CharValCompare.conjP_conjP]
        rw [if_pos hv, if_pos hv.symm]
        simp
      · have hv' : ¬ ∃ P ∈ SB, P.asIdeal.under (𝓞 X.F) = v.asIdeal := by
          rintro ⟨P, hP, e⟩
          rcases (hsp P).1 e with rfl | rfl
          exacts [hv (Or.inl hP), hv (Or.inr hP)]
        obtain ⟨ha, hb⟩ := not_or.1 hv
        obtain ⟨u1, s1⟩ := hU _ ha hb
        obtain ⟨u2, -⟩ := hU _ hb (by rwa [GlobalTheory.CharValCompare.conjP_conjP])
        rw [if_neg hv']
        simp only [hg, GlobalTheory.CharValCompare.conjP_conjP]
        rw [if_neg hv, if_neg fun h => hv (Or.symm h), GlobalTheory.OrdDetConj.ordDet_conjP hN,
          GlobalTheory.HeckeSplit.val_eq_inv_of_split X.F X.E χ v _ _ hT u1 u2 (Ne.symm hc) hm, pow_toNat_mul,
          Units.val_zpow_eq_zpow_val, map_zpow₀, s1, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, inv_zpow]
  have hinj : Function.Injective sel := fun v w h => HeightOneSpectrum.ext (by rw [← hsel v, h, hsel w])
  have e3 : σ (muOff sel SB mU N) = (((∏ᶠ w, g w)⁻¹ : ℂˣ) : ℂ) := by
    change σ (∏ᶠ v, GlobalTheory.MuOffMove.term sel SB mU N v) = _
    rw [finprod_group hX hsel g hfin h1, ← finprod_inv_distrib,
      map_finprod σ (GlobalTheory.MuOffMove.term_finite hsel SB mU hN), finprod_congr e2]
    exact ((Units.coeHom ℂ).map_finprod_of_injective Units.val_injective
      fun v => (g (sel v) * g (conjPrime₂ (sel v)))⁻¹).symm
  rw [e3, e1, Finset.prod_coe_sort SB fun P => ((χ.locK P (LinearEquiv.det (fr P)) : ℂˣ) : ℂ)⁻¹]
  simp [mul_comm]

end GlobalTheory.DetIdlValue
end
end

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

theorem _root_.GlobalTheory.T.cm_theta_translates_prime_to_q_integral : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]), Per D.host.d ι δ₀ θ Ω → ∀ (s : ℂ) (n : ℕ), Nat.Coprime n q → (n : ℂ) * s ∈ B.L.lattice → LatInt ι (Ω / ι δ₀) (lamOf D cc δ) (Formalism.L2.Th1.F.opU B.L s B.th0) := by
  first | exact @GlobalTheory.MomN.latInt_opU_of_coprime | exact GlobalTheory.MomN.latInt_opU_of_coprime | (intros; apply GlobalTheory.MomN.latInt_opU_of_coprime <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.adelicPeriodic_continuous_eq_zero_of_fourier_coeff : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F), Ctx ψ lam ν a → ∀ D : Set (Fin N → AF F), IsAddFundamentalDomain (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))) D (muV N ν) → muV N ν D = 1 → ∀ P : (Fin N → AF F) → ℂ, Continuous P → (∀ ξ u, P (rat ξ + u) = P u) → (∀ ξ : Fin N → F, ∫ u in D, P u * ψ (-(Bd (AF F) a u (rat ξ))) ∂(muV N ν) = 0) → P = 0 := by
  first | exact @GlobalTheory.SWQ.periodic_eq_zero_of_coeff | exact GlobalTheory.SWQ.periodic_eq_zero_of_coeff | (intros; apply GlobalTheory.SWQ.periodic_eq_zero_of_coeff <;> assumption)
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem classItemsAt_all : ∀ (D : D7) (n : ℕ), ClassItemsAt D n := fun D n =>
  have h := GlobalTheory.T.classNumber_finite_and_genusMass D
  ⟨genusMassAt_of D (GlobalTheory.genusMassStd_all D) n, classFinAt_of D h.1 n, classMassAt_of D h.2 n⟩

end GlobalTheory
end
