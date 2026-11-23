module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle031
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousNormFin
public import Formalism.LocalToGlobal.UnitaryNorms.CharShare
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle114
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle120
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbeddingClosedIntegral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle293
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle176
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle066
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMemPlacesOverOfNe
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle004

@[expose] public section

section



section
namespace Formalism.L2
def NGalTiedAlt.TupLink {D : Formalism.BasicNotions.D7} (G : _root_.Formalism.L2.NGalTiedAlt D) {C : Host.CharFrame D} {nch : Formalism.BasicNotions.NChoice D}
    (Tp : Host.TupTied D C nch) : Prop :=
  G.tup = Tp.tup
end Formalism.L2
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.HeightCounting
theorem twist_settings_unread_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (N : TwNew D), (∃ A' : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding N.toD7 (N.cf cf) jE, A'.row = N.row A.row ∧ (∀ lam, A'.pl.ι lam = A.pl.ι lam) ∧ (∀ w a, A'.wdT.e w a = A.wdT.e w a) ∧ (∀ j h1 h2 π, A'.au.cls j h1 h2 π = A.au.cls j h1 h2 π) ∧ ∀ hL, (Nonempty (_root_.GlobalTheory.HeightCounting.CGTrueT hL D A.wdT) → Nonempty (_root_.GlobalTheory.HeightCounting.CGTrueT hL N.toD7 A'.wdT)) ∧ (_root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL D A.wdT A.au → _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL N.toD7 A'.wdT A'.au)) ∧ (∀ M tup Q, MtInput D M tup Q → MtInput N.toD7 (N.mt M) tup Q) ∧ (BlocksUnique D → BlocksUnique N.toD7) := by
  intro D cf jE A N
  let A' : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding N.toD7 (N.cf cf) jE :=
    { bare := A.bare
      wdT := A.wdT
      lab := A.lab
      chr := { A.chr with }
      row := N.row A.row
      pl := { A.pl with }
      iota := A.iota
      wd := { A.wd with }
      grp := { A.grp with }
      par := { A.par with }
      au := { A.au with }
      chiT := A.chiT }
  refine ⟨⟨A', rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ _ _ => rfl, fun hL => ⟨fun ⟨h⟩ => ⟨{ h with }⟩, fun h => h⟩⟩,
    fun M tup Q h => { h with }, fun h => h⟩
end GlobalTheory.HeightCounting
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.HeightCounting


theorem typesOpen_withLoc_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)) (Sp : NdSpec A.pl M C big L.X L.T) (Au : _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup Sp.iq L.Y L.C), (∀ σ lam, IsSSRep (L.Z.rbar σ lam)) → Nonempty (TypesOpen (withLoc L) jE) := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp _ _ _ _ _ _ big L Sp Au hss
  refine ⟨{ grp := ?_, par := ?_, plB := A.pl.plB, plκ := A.pl.plκ, plB_loc := ?_, plB_iota := ?_, rbarSS := ?_, rbar := ?_ }⟩
  · exact ⟨A.grp.tA, A.grp.tκ, A.grp.teichC_def, A.grp.ζ, A.grp.ζ_gen, A.grp.O, A.grp.eSer_def, A.grp.kv, A.grp.tg_tame, A.grp.O_equiv, A.grp.O_tw⟩
  · exact ⟨A.par.eM, A.par.eM_K, A.par.eP, A.par.locPar_def⟩
  · exact Au.kFbar
  · exact fun i k v x => A.iota _ k v x
  · exact fun σ lam _ => hss σ lam
  · exact fun i σ _ _ Sig ρ hP hR g => (L.rbar_tie i σ Sig ρ hP hR).2 g
end GlobalTheory.HeightCounting
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeightCounting.NchAt

theorem tie_of_true_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D' : D7} {cf' : CharFrame D'} {C' : NChoice D'} {tp' : TupTied D' cf' C'}
    (b : _root_.GlobalTheory.HeightCounting.NormChoiceRealisation hL D' cf' C' tp') : NChTie D' C' ∧ PsiChoiceCompatible D' cf' C' tp' := by
  obtain ⟨⟨D, cf, jE, A, cg, au, rep, row, low, Pq, S, hL', eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩, pack⟩ := b
  subst eq
  cases pack
  refine ⟨⟨Sp.twOf_eq, Sp.twSide_eq, fun a => ?_, ?_, ch.nct.embedding_baseField_condition⟩, ch.psi⟩
  · exact (Sp.Q_eq _ _ a (((L.X.nd.locs_mem _ _ a).2 ⟨rfl, rfl⟩))).trans (Sp.Qc_eq _ _)
  · obtain ⟨ψ0, hc, hw, -⟩ := ch.nct.psi_eq
    exact ⟨ψ0, hc, hw, fun a g => Sp.psi_eq a g _ (hw _ g)⟩
end GlobalTheory.HeightCounting.NchAt
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
namespace GlobalTheory.EtaTildeShift
theorem sh_half_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (t : D.what₂.Tau) (sh : ℂ),
    D.naut.infG D.naut.etaT (embT D t) = {sh} → ∃ z : ℤ, sh = (z : ℂ) + 1 / 2 := by
  intro D cf jE A t sh h
  have hE : (A.chr.e1 D.naut.etaT).1.HasInfQ (embPsi D.host) (fun _ => (1 / 2 : ℚ)) :=
    ⟨fun _ => 1, fun _ => by norm_num, by rw [A.chr.etaT]; exact cf.isEta.inf⟩
  have h2 := (A.chr.infG _ _ hE (D.eTau t)).1
  have h3 : D.naut.infG D.naut.etaT (embT D t) = {((1 / 2 : ℚ) : ℂ)} := h2
  rw [h3] at h
  have := (Multiset.singleton_inj.1 h).symm
  refine ⟨0, ?_⟩
  rw [this]; push_cast; ring
end GlobalTheory.EtaTildeShift
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.MuCLoc
theorem exists_muC_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc), ∃ μ : D.naut.CG 1, D.naut.csd μ ∧ ∀ j : Fin D.R.m, j.1 + 1 = X.nd.j i → (A.chr.e1 μ).1 = tp.tup (X.nd.mu i) j := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i
  obtain ⟨h1, h2⟩ := X.nd.j_range i
  let j : Fin D.R.m := ⟨X.nd.j i - 1, by omega⟩
  refine ⟨A.chr.e1.symm ⟨tp.tup (X.nd.mu i) j, tp.tup_unitary (X.nd.mu i) j⟩, ?_, ?_⟩
  · rw [A.chr.csd, Equiv.apply_symm_apply]
    exact GlobalTheory.CsdTriv.isCSD_of_trivOn _ _ _ ((cf.isMu0 j).triv.mul (tp.xi_triv (X.nd.mu i)))
  · intro j' hj'
    have : j' = j := Fin.ext (by simp only [j]; omega)
    subst this
    rw [Equiv.apply_symm_apply]
end GlobalTheory.MuCLoc
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.ChiOneRead
theorem chiOne_read_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (hψ : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (tp.psi w).ValuesIn 0 D.what₂.embLL) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (j : Fin D.R.m), j.1 + 1 = X.nd.j i → ∃ Bf : Finset (HeightOneSpectrum (𝓞 D.host.E)), ∀ P ∉ Bf, (tp.tup (X.nd.mu i) j * cf.eta⁻¹).UnrAt P ∧ ∀ σ : Formalism.ConjugateSelfDual.G D.host.E X.nd.Om, IsFrob (F := D.host.E) (X.nd.plOm.1 P) (normV P) σ → (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) (Sp.iq i (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)) ((X.nd.chi i 1 σ : (X.nd.O i)ˣ) : X.nd.O i))) = (((tp.tup (X.nd.mu i) j * cf.eta⁻¹).val P)⁻¹ : ℂˣ).1 * ((normV P : ℕ) : ℂ) ^ (((((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2) : ℝ) : ℂ) := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh hψ big X T Sp i j hj
  classical
  obtain ⟨B1, h1⟩ := Bs.chi.chi1 (T.twOf i) (X.nd.j i) (T.twSide i) (X.nd.j_range i).1 (X.nd.j_range i).2
  have hpsi := tp.psi_is (X.nd.w i) (X.nd.w_tw i)
  have hfin := Formalism.L2.NC.finite_placesOver (E := D.host.E) (X.nd.l i)
  refine ⟨B1 ∪ C.Q (X.nd.w i) ∪ hfin.toFinset, fun P hP => ?_⟩
  have hP1 : P ∉ B1 := fun h => hP (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hPQ : P ∉ C.Q (X.nd.w i) := fun h => hP (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hPl : P ∉ placesOver D.host.E (X.nd.l i) := fun h => hP (Finset.mem_union_right _ (hfin.mem_toFinset.2 h))
  obtain ⟨α, hα, x, hx, hσ⟩ := h1 P hP1
  have hxi : tp.xi (X.nd.mu i) = cf.delAt (X.nd.l i) * tp.psi (X.nd.w i) := by
    rw [X.nd.mu_w i, tp.xi_tw, X.nd.w_l i]
  have hl' : D.ntw.l (T.twOf i) = X.nd.l i := T.twOf_l i
  have key : ∀ z : (AdeleRing (𝓞 D.host.E) D.host.E)ˣ, (Bs.chiD.firstHeckeCharacter (T.twOf i) (X.nd.j i)).χ z =
      (cf.mu0 j).1 z * (cf.delAt (X.nd.l i)).1 z * (cf.eta.1 z)⁻¹ := by
    intro z
    change (Bs.chiD.mu0 (X.nd.j i)).χ z * (Bs.chiD.del (T.twOf i)).χ z * ((Bs.chiD.etaT).χ z)⁻¹ = _
    rw [← hj, Bs.ringSpec_normalisedCharacter_eq j z, Bs.eta_eq]
    have hd := Bs.del_eq (T.twOf i) z
    rw [hl'] at hd
    erw [hd]
  have hloc : ∀ (χ : HChar D.host.E) (u : (P.adicCompletion D.host.E)ˣ),
      χ.loc P u = χ.1 (Units.map (Formalism.L2.NC.locM P) u) := fun χ u => by
    rw [← localIdele_eq]; rfl
  have hunr : (tp.tup (X.nd.mu i) j * cf.eta⁻¹).UnrAt P := by
    intro u hu
    have e1 := hα.1 u hu
    rw [key] at e1
    have e2 : (tp.psi (X.nd.w i)).loc P u = 1 := ((hpsi.ram P).2 hPQ) u hu
    rw [hloc] at e2
    rw [hloc]
    show (cf.mu0 j * tp.xi (X.nd.mu i) * cf.eta⁻¹).1 _ = 1
    rw [hxi]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, MonoidHom.mul_apply, MonoidHom.inv_apply] at e1 e2 ⊢
    rw [e2, mul_one]
    exact e1
  refine ⟨hunr, fun σ hσF => ?_⟩
  have hϖ : IsUnifAt P (atFin P (unif P)) := unif_spec P
  have hαv : α = ((cf.mu0 j).val P : ℂ) * ((cf.delAt (X.nd.l i)).val P : ℂ) * ((cf.eta.val P : ℂˣ) : ℂ)⁻¹ := by
    rw [← hα.2 _ hϖ, key]
    simp only [HChar.val, HChar.locK, HChar.loc, MonoidHom.comp_apply, localIdele_eq, Units.val_mul,
      Units.val_inv_eq_inv_val]
  have hc : ((X.nd.chi i 1 σ : (X.nd.O i)ˣ) : X.nd.O i) =
      T.twist₂ i (((lay0 D).ntw.chi1 (T.twOf i) (X.nd.j i) (T.twSide i) σ : ((lay0 D).ntw.O0 (T.twOf i))ˣ) : (lay0 D).ntw.O0 (T.twOf i)) *
        (T.psiL i σ : X.nd.O i) := by
    rw [T.chi_tw i]; rfl
  have hR1 : (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) (Sp.iq i (algebraMap (X.nd.O i) (FractionRing (X.nd.O i))
      (T.twist₂ i (((lay0 D).ntw.chi1 (T.twOf i) (X.nd.j i) (T.twSide i) σ : ((lay0 D).ntw.O0 (T.twOf i))ˣ) : (lay0 D).ntw.O0 (T.twOf i))))) =
      D.what₂.embLL (x : D.what₂.LL) := by
    have e := T.twO_emb i x (((lay0 D).ntw.chi1 (T.twOf i) (X.nd.j i) (T.twSide i) σ : ((lay0 D).ntw.O0 (T.twOf i))ˣ) : (lay0 D).ntw.O0 (T.twOf i)) (hσ σ hσF)
    rw [← e, Sp.iq_LL]
  obtain ⟨ψ0, -, h2, -⟩ := hCS.nct.psi_eq
  have hR2 : (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) (Sp.iq i (algebraMap (X.nd.O i) (FractionRing (X.nd.O i))
      (T.psiL i σ : X.nd.O i))) = D.what₂.embLL ((ψ0 (X.nd.w i) σ : (D.what₂.LL)ˣ) : D.what₂.LL) := by
    have e3 := Sp.psi_eq i σ _ (h2 (X.nd.w i) σ)
    rw [← e3, Sp.iq_LL]
  obtain ⟨y, hy⟩ := hψ (X.nd.w i) (X.nd.w_tw i) P ((hpsi.ram P).2 hPQ)
  have hy' : D.what₂.embLL y⁻¹ = ((((tp.psi (X.nd.w i)).val P)⁻¹ : ℂˣ) : ℂ) := by
    rw [map_inv₀, hy]
    simp [HChar.valTw]
  have hl2 : P ∉ placesOver D.host.E (D.what₂.places.resChar (X.nd.w i)) := by rw [X.nd.w_l i]; exact hPl
  have e4 := hCS.psi (X.nd.w i) (X.nd.w_tw i) P hPQ hl2 (X.nd.plOm.1 P) σ (X.nd.plOm.2 P) hσF y⁻¹ hy'
  have e5 : ((ψ0 (X.nd.w i) σ : (D.what₂.LL)ˣ) : D.what₂.LL) = y⁻¹ :=
    (C.embW (X.nd.w i)).injective (by rw [e4]; exact h2 _ σ)
  rw [hc, map_mul, map_mul, map_mul, hR1, hR2, e5, hy']
  have hx' : D.what₂.embLL (x : D.what₂.LL) = α⁻¹ * ((Real.sqrt (normV P) : ℝ) : ℂ) ^ (-(D.R.r : ℤ)) := hx
  rw [hx', ← sqrt_zpow (normV P) D.R.r D.R.t D.R.nV rfl, hαv]
  simp only [TupTied.tup, hxi, HChar.val_mul, HChar.val_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  ring
end GlobalTheory.ChiOneRead
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.AutUnr


theorem locV_unr_m_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (ι : Type) [Finite ι] (F : ι → Submodule ℂ (GAf D.host.E D.R.nV → (mlX M X i).wt.W)) (irr : ∀ P, NG.IsIrrRep (mlX M X i).wt.ρ (F P)) (hinj : ∀ P P', NG.IsoRep (F P) (F P') → P = P') (hsurj : ∀ S', NG.IsIrrRep (mlX M X i).wt.ρ S' → (NG.isoTyp (mlX M X i).wt.ρ S').comap (mlX M X i).real ≠ ⊥ → ∃ P, NG.IsoRep (F P) S') (hne : ∀ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real ≠ ⊥) (hind : iSupIndep (fun P => (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real)) (htop : ⨆ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real = ⊤) (P : ι) (w : PlE D.host), IsSplitPl D.host w → w ∉ X.nd.Q i → (∀ k, w ∉ placesOver D.host.E (D.host.g k)) → w ∉ placesOver D.host.E (if X.nd.l i = D.host.pde then D.host.pde' else D.host.pde) → D.naut.unr (D.nbc.locAU (X.nd.j i) (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 { (mlX M X i).wt with S := F P, irrS := irr P }) w) := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i ι _ F irr hinj hsurj hne hind htop P w hw hQ hg hp
  classical
  obtain ⟨s, hsw⟩ := exists_splitPlace_eq D w hw
  have hov : NG.OverPl w s.v := hsw ▸ s.w_under
  have hjf : X.nd.j i - 1 + 1 = X.nd.j i := by have := X.nd.j_range i; omega
  let jf : Fin D.R.m := ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩
  have h0 := hMI.hyp (X.nd.w i) jf
  have hyp : NG.HypOutside (mlX M X i).J (mlX M X i).χ (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) jf)) :=
    GlobalTheory.FitHecke.hypOutside_transport' (M := M) (X.nd.mu_w i).symm hjf _ _ (X.nd.j_range i).1 (X.nd.j_range i).2 _ h0
  have hi : i ∈ X.nd.locs (X.nd.j i) (X.nd.w i) := (X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
  have hQe : C.Q (X.nd.w i) = Sp.B.Qc (X.nd.j i) (X.nd.w i) := (Sp.Qc_eq _ _).symm
  have hvB : s.v ∉ gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) jf) := by
    rintro (⟨w', hov', k, hk⟩ | hq)
    · exact hg k (mem_placesOver_of_overPl hov hov' hk)
    · obtain ⟨w', hov', hw'⟩ := GlobalTheory.FitHecke.qPl_sub tp (X.nd.w i) (X.nd.w_tw i) jf hq
      rcases hw' with hQ' | hp'
      · rw [hQe] at hQ'
        have hwQ : w ∈ Sp.B.Qc (X.nd.j i) (X.nd.w i) := Sp.B.Qc_over _ _ w' w hQ' ⟨s.v, hov', hov⟩
        rw [← Sp.Q_eq _ _ i hi] at hwQ
        exact hQ hwQ
      · rw [X.nd.w_l i] at hp'
        exact hp (mem_placesOver_of_overPl hov hov' hp')
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hne P)
  have hfix : ∀ κ ∈ {κ : GAf D.host.E D.R.nV | κ ∈ Umax D.host.E D.R.nV ∧ TrivOutside {s.v} κ},
      NG.rt D.host.E D.R.nV κ ((mlX M X i).real y) = (mlX M X i).real y := by
    rintro κ ⟨hU, htr⟩
    have htr' : TrivOutside (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) jf))ᶜ κ := by
      intro v hv
      apply htr v
      rintro rfl
      exact hv hvB
    obtain ⟨hJ, hχ⟩ := hyp κ htr'
    have hκ : κ ∈ (mlX M X i).J := hJ.2 hU
    have hmem : (mlX M X i).real y ∈ NG.TypeSp (mlX M X i).wt.ρ (mlX M X i).J (mlX M X i).χ := by
      rw [← (mlX M X i).real_range]; exact ⟨y, rfl⟩
    have e := hmem.2 ⟨κ, hκ⟩
    rw [hχ hκ] at e
    simpa using e
  have hr0 : (mlX M X i).real y ≠ 0 := fun h =>
    hy0 ((mlX M X i).real_inj (h.trans (map_zero _).symm))
  obtain ⟨f, hf, hf0, hff⟩ := exists_fixed_of_isoTyp (mlX M X i).wt.ρ (irr P).1.stable _ hy hr0 hfix
  have hsph : _root_.UpperTheory.One.M.SphAtG { (mlX M X i).wt with S := F P, irrS := irr P } s.v :=
    _root_.UpperTheory.One.M.New.sphMk ⟨f, hf, hf0, fun κ hU htr => hff κ ⟨hU, htr⟩⟩
      fun h => absurd rfl (h s)
  rw [← hsw]
  exact A.au.locUnr _ _ _ _ s hsph
end GlobalTheory.AutUnr
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal
namespace GlobalTheory.ChiLocGal
section General
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
end General
section Values
variable {E : Type} [Field E] [NumberField E]
end Values
theorem chi1_loc_isGal_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T), ∀ (Y : LocAut X) (Cb : LocBC Y), _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup Sp.iq Y Cb → ∀ (art : Ideles D.host.E →* Gab D.host.E D.nd.Om), IsGlobalArtin art → ∀ (i : X.nd.Loc) (j' : Fin D.R.m), j'.1 + 1 = X.nd.j i → ∃ n, GlobalTheory.GalChar.IsGal art (Sp.iq i) (Y.naut.iotaQC i) (GlobalTheory.GalChar.block (cf.mu0 j' * cf.delAt (X.nd.l i)) cf.eta D.R.r) n ((Units.map (T.twist₂ i).toMonoidHom).comp (D.ntw.chi1 (T.twOf i) (X.nd.j i) (T.twSide i))) := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp _ _ _ he _ _ big X T Sp Y Cb hAu art ha i j' hj
  letI := D.ntw.crO0 (T.twOf i)
  haveI := D.ntw.twistBaseCoefficientRing_isDomain (T.twOf i)
  haveI := D.ntw.twistBaseCoefficientRing_isDVR (T.twOf i)
  letI := D.ntw.topO0 (T.twOf i)
  haveI := D.ntw.twistBaseCoefficientRing_topologicalRing (T.twOf i)
  let C' : GlobalTheory.Mem.Chr.HFrame D.host (eExp D) :=
    ⟨cf.P, cf.W, cf.mu0, cf.eta, cf.chiPsi, cf.del, cf.del', cf.isMu0, cf.isEta, cf.isChi, cf.isDel, cf.isDel'⟩
  obtain ⟨n0, h0⟩ := GlobalTheory.GalChar.exists_isAlgPos_mu0 C' he j'
  obtain ⟨n, hn⟩ := GlobalTheory.GalChar.block_alg C' ⟨_, GlobalTheory.GalChar.isAlgPos_mul h0 (GlobalTheory.GalChar.del_alg C' (X.nd.l i))⟩
  have hn' : IsAlgPos (GlobalTheory.GalChar.block (cf.mu0 j' * cf.delAt (X.nd.l i)) cf.eta D.R.r) n := hn
  have hj1 := X.nd.j_range i
  obtain ⟨B1, hB1⟩ := Bs.chi.chi1 (T.twOf i) (X.nd.j i) (T.twSide i) hj1.1 hj1.2
  have hχ : ∀ x, (Bs.chiD.firstHeckeCharacter (T.twOf i) (X.nd.j i)).χ x = (cf.mu0 j' * cf.delAt (X.nd.l i) * cf.eta⁻¹).1 x := by
    intro x
    have h1 := Bs.ringSpec_normalisedCharacter_eq j' x
    have h2 := Bs.del_eq (T.twOf i) x
    have h3 := Bs.eta_eq x
    rw [hj] at h1
    have h4 : D.ntw.l (T.twOf i) = X.nd.l i := T.twOf_l i
    rw [h4] at h2
    change (Bs.chiD.mu0 (X.nd.j i)).χ x * (Bs.chiD.del (T.twOf i)).χ x *
      (Bs.chiD.etaT.χ x)⁻¹ = (cf.mu0 j').1 x * (cf.delAt (X.nd.l i)).1 x * (cf.eta.1 x)⁻¹
    rw [h1, h2, h3]
  set χb := GlobalTheory.GalChar.block (cf.mu0 j' * cf.delAt (X.nd.l i)) cf.eta D.R.r with hχb
  have key : ∀ P ∉ B1, ∃ x : ↥D.LL0, Formalism.L2.NC.complexEmbeddingRestrictedToSubfield D x = ((χb.val P : ℂˣ) : ℂ)⁻¹ ∧
      ∀ σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om, IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) σ →
        X.nd.embK i (x : D.what₂.LL) = algebraMap (X.nd.O i) (FractionRing (X.nd.O i))
          (T.twist₂ i (Units.val (D.ntw.chi1 (T.twOf i) (X.nd.j i) (T.twSide i) σ))) := by
    intro P hP
    obtain ⟨α, hα, x, hx, hσ⟩ := hB1 P hP
    refine ⟨x, ?_, fun σ hσ' => T.twO_emb i x _ (hσ σ hσ')⟩
    rw [val_block (val_of_at hχ hα) hx, inv_inv]
  have hev : ∀ᶠ P in Filter.cofinite, P ∉ B1 := Filter.eventually_cofinite.2 (by simpa using B1.finite_toSet)
  have hAlm : GlobalTheory.GalChar.AlmostIn (Formalism.L2.NC.complexEmbeddingRestrictedToSubfield D) χb := by
    filter_upwards [hev] with P hP
    obtain ⟨x, hx, -⟩ := key P hP
    exact ⟨x⁻¹, by rw [map_inv₀, hx, inv_inv]⟩
  have hf : ∀ x : ↥D.LL0, Y.naut.iotaQC i (Sp.iq i (((X.nd.embK i).comp D.LL0.val.toRingHom) x)) =
      Formalism.L2.NC.complexEmbeddingRestrictedToSubfield D x := by
    intro x
    rw [← hAu.iotaQ i]
    exact Y.iota_LL i x
  have hO := X.nd.O_adic i
  have hκ := Sp.iq_alg i
  obtain ⟨r0, hr0⟩ := GlobalTheory.GalChar.exists_isGal hO hκ ha hn' hf hAlm
  haveI : T2Space (X.nd.O i) := (GlobalTheory.GalChar.isEmbedding_toQ hO hκ).t2Space
  have hlO := (GlobalTheory.CoefEmbed.embedding_closed_integral (X.nd.l i) (X.nd.O i) hO (Sp.iq i) hκ).2.2.2
  have hl0 : ((X.nd.l i : ℕ) : D.ntw.O0 (T.twOf i)) ≠ 0 := fun h => by
    have h' := congrArg (algebraMap (D.ntw.O0 (T.twOf i)) (FractionRing (D.ntw.O0 (T.twOf i)))) h
    rw [map_natCast, map_zero, ← map_natCast (D.ntw.emb0 (T.twOf i))] at h'
    have h'' := (D.ntw.emb0 (T.twOf i)).injective (h'.trans (map_zero _).symm)
    exact (Fact.out : (X.nd.l i).Prime).ne_zero (by exact_mod_cast h'')
  have hc1 : Continuous ((Units.map (T.twist₂ i).toMonoidHom).comp (D.ntw.chi1 (T.twOf i) (X.nd.j i) (T.twSide i))) :=
    GlobalTheory.GalChar.continuous_units _ ((GlobalTheory.GalChar.continuous_ringHom (D.ntw.twistBaseCoefficientRing_isAdic (T.twOf i)) hO hl0 hlO (T.twist₂ i)).comp
      (D.ntw.twistCharacterFamily_continuous (T.twOf i) (X.nd.j i) (T.twSide i)))
  have hlne : X.nd.l i ≠ 0 := (Fact.out : (X.nd.l i).Prime).ne_zero
  have heq : r0 = (Units.map (T.twist₂ i).toMonoidHom).comp (D.ntw.chi1 (T.twOf i) (X.nd.j i) (T.twSide i)) := by
    refine GlobalTheory.GalChar.eq_of_frob ha (GlobalTheory.GalChar.continuous_units r0 hr0.2.1) hc1 ?_
    filter_upwards [hev, GlobalTheory.GalChar.unr_ae χb, GlobalTheory.GalChar.away_ae (E := D.host.E) (X.nd.l i) hlne]
      with v hv hu hl A' hA' σ hσ
    refine frob_any (D.nd.plOm.2 v) hA' (fun σ' hσ' => ?_) hσ
    obtain ⟨x, hx1, hx2⟩ := key v hv
    apply Units.ext
    apply GlobalTheory.GalChar.toQ_injective (Sp.iq i)
    apply (Y.naut.iotaQC i).injective
    rw [hr0.frob ha (Or.inl hl) hu (D.nd.plOm.2 v) hσ', ← hx1]
    show _ = Y.naut.iotaQC i (Sp.iq i (algebraMap (X.nd.O i) (FractionRing (X.nd.O i))
      (T.twist₂ i (Units.val (D.ntw.chi1 (T.twOf i) (X.nd.j i) (T.twSide i) σ')))))
    rw [← hx2 σ' hσ']
    exact (hf x).symm
  exact ⟨n, heq ▸ hr0⟩
end GlobalTheory.ChiLocGal
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.HeightCounting.TwistAny
open Formalism.L2.NR
theorem exists_isRepOf_tw_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE), GalEx D → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (π : D.naut.CG D.R.r), D.naut.csd π → D.naut.ralg π → ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (Qbar l), IsRepOf D l ι (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2) ρ := by
  intro hGA D cf jE A hGal l _ ι π hc hr
  obtain ⟨ρ₁, c1, ss1, f1⟩ := hGal l ι D.R.r (Formalism.L2.NR.one_le_r D) π hc hr
  obtain ⟨n, hn⟩ := (GlobalTheory.Mem.CharAlg.isAlg_even_odd D.R D.host).2 cf.eta cf.isEta.inf D.R.t D.R.t_odd
  obtain ⟨art, ha⟩ := hGA D.host.E D.nd.Om
  obtain ⟨μ, hμc, hμ⟩ := ha.exists_isLAdicOf ι (GlobalTheory.HeckeGal.isAlgPos_of_isAlg hn)
  refine ⟨Formalism.MainNotions.SumRepresentations.At.twGL ρ₁ μ, ?_, GlobalTheory.TwistLG.isSSRep_twGL _ _ ss1, ?_⟩
  · simp only [GlobalTheory.TwistLG.twGL_val]
    exact (Units.continuous_val.comp hμc).smul c1
  have hfin := placesOver_finite D.host.E l (Fact.out : l.Prime).ne_zero
  filter_upwards [f1, D.naut.locG_unr_ae π, hfin.compl_mem_cofinite] with w hw1 hu hwl
  intro B σ hB hσ
  have hwl' : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := hwl
  have hue : D.naut.unr (D.naut.locG D.naut.etaTinv w) := (D.naut.etaTinv_def w).1
  have hU := (A.chr.unr_iff _ w).1 hue
  have hf := A.chr.frob _ w hU
  rw [A.chr.etaTinv] at hf hU
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow D.host.E (-(D.R.t : ℝ) / 2)
  have hψu : (cf.eta⁻¹ * GlobalTheory.HeckeGal.Model.absPow D.host.E (-(D.R.t : ℝ) / 2)).UnrAt w := by
    intro x hx
    change (cf.eta⁻¹).loc w x * (GlobalTheory.HeckeGal.Model.absPow D.host.E (-(D.R.t : ℝ) / 2)).loc w x = 1
    rw [hU x hx, hν.1 w x hx, one_mul]
  have hμv := hμ.frob_unr ha (Or.inl hwl') hψu hB hσ
  set u : ℂ := (((cf.eta⁻¹ * GlobalTheory.HeckeGal.Model.absPow D.host.E (-(D.R.t : ℝ) / 2)).val w : ℂˣ) : ℂ)⁻¹ with hu_def
  have hu1 : D.naut.frobEig (D.naut.lpTw (D.naut.locG D.naut.etaTinv w) (-(D.R.t : ℝ) / 2)) = {u} := by
    rw [D.naut.frobEig_tw _ _ hue, hf, Multiset.map_singleton]
    congr 1
    rw [hu_def, HChar.val_mul, HChar.val_inv, Units.val_mul, hν.2.1 w]
    have hn' : (Ideal.absNorm w.asIdeal : ℕ) = normV w := by
      simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [hn', mul_inv, Units.val_inv_eq_inv_val, Complex.cpow_neg, inv_inv]
  have hχu : ι ((μ σ : (Qbar l)ˣ) : Qbar l) = u := by
    rw [hμv, map_inv₀, ι.apply_symm_apply]
  have h1 := hw1 B σ hB hσ
  rw [GlobalTheory.TwistLG.twGL_val, ← Matrix.charpoly_map, GlobalTheory.ParamRep.map_smul_matrix,
    GlobalTheory.ParamRep.galPol_twist D.nd D.naut π hu u hu1]
  have h2 : ((((ρ₁ σ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).map ι.toRingHom)).charpoly =
      ((D.naut.frobEig (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2))).map fun α => X - C α).prod := by
    rw [Matrix.charpoly_map]; exact h1
  have h3 := GlobalTheory.ParamRep.charpoly_smul_of_prod _ u _ h2
  have hχu' : ι.toRingHom ((μ σ : (Qbar l)ˣ) : Qbar l) = u := hχu
  rw [hχu']
  exact h3
end GlobalTheory.HeightCounting.TwistAny
end
end
end
