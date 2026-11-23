module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle290
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle135
import Formalism.LocalToGlobal.Columns.CoefColLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle172
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle061
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle329
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle118
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle195
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle004

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.TC.ChTw.Match

variable {B : Base} {X : PreX B.toPre}

def LocalCondMoveDecoratedLattice (u : B.Word) (n : ℕ) (s : GA B n) (h : GLG (E := B.fields.E) (n := n) (SG := (B.primes X).vGs)) : Prop :=
  s ∈ Formalism.L2.Herm.UstdAf B.sp.cm n ∧ Formalism.L2.Herm.Carries s (stdLat B.fields.E n) (stdLat B.fields.E n) ∧
  (∀ (P : (B.primes X).vT u) (r j : Fin n), r.1 + 1 = n →
    HasRes P.1 (adAt B.host.F P.1 ((s⁻¹ : GA B n).1 r j)) (if j = r then 1 else 0)) ∧
  ∀ (w : (B.primes X).vGs) (r j : Fin n), HasRes w.1 (adAt B.host.F w.1 ((s⁻¹ : GA B n).1 r j)) ((h w).1 r j)

def LocCQ (Q : Finset (HeightOneSpectrum (𝓞 B.fields.E))) (n : ℕ) (s : GA B n) (θ : GLQ B.fields.E n Q) : Prop :=
  ∀ (P : Q) (r j : Fin n), adAt B.host.F P.1 ((s : Matrix (Fin n) (Fin n) _) r j) =
    algebraMap B.host.E _ ((((θ P)⁻¹ : ↥(GLint B.fields.E n P.1)).1) (Pi.single j 1) r)

end GlobalTheory.Mem.Col2.TC.ChTw.Match
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.PerLaw

variable {B : Base} {X : PreX B.toPre} {I : TC B X}

theorem piT_notMem_Q (h : I.Ok) (u : B.Word) (a : I.ι) (P : I.Q a) : (B.primes X).piT u ∉ P.1.asIdeal := fun hm => by
  have hPr := (base_fields_primes_ok B X).2.1
  refine T_notMem_QE I.sel (I.tup a) u hPr h.sel_ok (h.T_mem u) P.1 P.2 ?_
  rw [← hPr.piT_norm u]
  exact P.1.asIdeal.mul_mem_right _ hm

theorem til_deco (h : I.Ok) (u : B.Word) (a : I.ι) (b : (I.perIn u a).S'.β) (p : (I.stX a).D b) :
    ((I.perIn u a).til b p).1.1.deco = DecoSet.tilH (N_m_succ B.R) ((B.primes X).piT u) p.1.1.deco :=
  tilF_deco I.sel (I.tup a) (base_fields_primes_ok B X).2.1 u (piT_notMem_Q h u a) p.1.1

theorem pref_m (u : B.Word) (a : I.ι) (b : (I.stp0 u a B.R.m).β) (q : (I.stp0 u a B.R.m).D b) :
    I.pref u a B.R.m b q ↔ ∃ d, q.1.1 = tilF (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u d := by
  have hm := B.R.two_le_m
  rw [← topLev_pref_m I.Ch I.sel (I.tup a) (I.cst a) I.Ps u]
  exact ⟨fun h => h.2.2, fun h => ⟨fun e => by omega, fun e => by omega, h⟩⟩

theorem stX_ok (a : I.ι) : (I.stX a).Ok := by
  have hX := (base_fields_primes_ok B X).1
  let y := Ys.triv B.fields (B.R.N B.R.m - 1)
  let Λ := rowTyG I.Ch I.Ps
  let Θ := levQX B.R I.sel (I.tup a)
  have hRoot (g : Θ.grp) : IsOfFinOrder (Θ.chr g) := by
    rw [show Θ.chr g = ∏ P, (Θ P).lam (piProj (fun P => (Θ P).H) P g) from
      piChar_apply (fun P => (Θ P).H) (fun P => (Θ P).lam) g]
    refine Finset.prod_induction _ IsOfFinOrder (fun _ _ => IsOfFinOrder.mul) IsOfFinOrder.one ?_
    intro P _
    obtain ⟨m, hm, hpow⟩ := levQX_root (R := B.R) I.sel (I.tup a) P
    exact isOfFinOrder_iff_pow_eq_one.2 ⟨m, hm, hpow _⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact stepY_fin_orb (ST := ∅) y Unit (fun _ => Λ) (fun _ => Θ) (fun _ => True) hX
      (fun _ => levQX_finiteIndex I.sel (I.tup a)) (fun _ _ => Set.finite_singleton _)
  · intro b p
    haveI : Finite (autO p.1.1.deco.1.N) := by
      first
      | exact autO_finite (posStar_of_ok hX) p.1.1.deco.full_lattice
      | exact autO_finite (posStar_of_ok hX) p.1.1.deco.full_lattice.toIsLattice
    exact Finite.of_injective _ (stabAut_inj y Unit (fun _ => Λ) (fun _ => Θ) (fun _ => True) b p)
  · intro _ g
    let M : Matrix (Fin (B.R.N B.R.m - 1)) (Fin (B.R.N B.R.m - 1)) B.fields.E := ↑(toGLm _ _ g.1.1)
    have h : Mᴴ * 1 * M = 1 := toGLm_mem_UJ g.1
    rw [Matrix.mul_one] at h
    exact h
  · intro _ g
    exact isOfFinOrder_iff_pow_eq_one.1
      ((MonoidHom.isOfFinOrder Λ.chr (isOfFinOrder_of_finite g.2.1)).mul (hRoot g.2.2))
  · intro _ g p x
    show (↑(toGLm _ _ g.1.1) : Matrix _ _ _) *ᵥ x ∈ (p.1.1.deco.1.act g.1.1 g.2.1.1).Lsh ↔
      x ∈ p.1.1.deco.1.Lsh
    rw [toGLm_mulVec, Deco.Lsh_act _ g.1.2, mem_gmap, LinearEquiv.symm_apply_apply]
  · intro _ p
    first
    | exact p.1.1.deco.2.Lsh_full_lattice
    | exact p.1.1.deco.2.Lsh_full_lattice.toIsLattice
  · intro b g p h h₁
    exact stepY_eq_one y Unit (fun _ => Λ) (fun _ => Θ) (fun _ => True) b g p h
      (Subtype.ext ((toGLm B.fields.E (B.R.N B.R.m - 1)).injective (h₁.trans (map_one _).symm)))



theorem perIn_ok (h : I.Ok) (u : B.Word) (a : I.ι) : (I.perIn u a).Ok := {
  step := stX_ok a
  til_smul _ g p := Subtype.ext (Prod.ext
    (tilF_extTop I.Ch I.sel (I.tup a) (I.cst a) I.Ps (base_fields_primes_ok B X).2.1 u (piT_notMem_Q h u a) g p.1.1)
    (Set.image_empty _).symm)
  ext_inj _ := extTop_injective I.Ch I.sel (I.tup a) (I.cst a) I.Ps
  gam_ini _ g x := (congrArg (iniH (N_m_succ B.R)) (toGLm_mulVec (extUH (N_m_succ B.R) g.1).1 x)).trans
    ((iniH_extUH _ g.1 x).trans (toGLm_mulVec g.1.1 _).symm)
  gam_last _ g x := (congrFun (toGLm_mulVec (extUH (N_m_succ B.R) g.1).1 x) _).trans (extUH_last _ g.1 x)
  chr_ext _ g := chr_extTop I.Ch I.sel (I.tup a) (I.cst a) I.Ps g
  tz_ne := by
    have hPr := (base_fields_primes_ok B X).2.1
    show star (((B.primes X).piT u : 𝓞 B.fields.E) : B.fields.E) ≠ 0
    rw [star_ne_zero]
    intro h
    have h1 : (B.primes X).piT u = 0 := RingOfIntegers.ext h
    have h2 := hPr.piT_norm u
    rw [h1, zero_mul] at h2
    exact (hPr.T_prime u).ne_zero (by exact_mod_cast h2.symm)
  Lsh_til b p x := by
    have hPr := (base_fields_primes_ok B X).2.1
    show x ∈ ((I.perIn u a).til b p).1.1.deco.1.Lsh ↔ _
    rw [til_deco h u a b p]
    exact tilH_Lsh _ p.1.1.deco (conj_piT_notMem hPr u) (piT_notMem_vGs hPr u)
      (fun P => decoFin_mem_of_mem_divs P.2) (piT_dvd_of_mem (base_fields_primes_ok B X).1 hPr u) x
  rep_til b p := by
    obtain ⟨d, hd⟩ := (pref_m u a _ _).1 (@pref_prefRep _ _ _ ((I.stp0 u a B.R.m).actD _)
      (I.pref u a B.R.m (idxTop I.sel (I.tup a) (I.idx a))) ((I.perIn u a).til b p) ((pref_m u a _ _).2 ⟨p.1.1, rfl⟩))
    exact ⟨(), trivPt _ _ _ _ _ d, (topPt_val I.sel (I.tup a) (I.cst a) u _).symm.trans
      (congrArg (topPt I.sel (I.tup a) (I.cst a) u) hd)⟩
  H_idx _ := (inferInstance : (⊤ : Subgroup _).FiniteIndex)
  H_rat _ g := ⟨g, Subgroup.mem_top _, rfl⟩ }



theorem perIn_over (h : I.Ok) (u : B.Word) (a : I.ι) : (I.perIn u a).Over (I.atIn u a) := {
  norm_tz := by
    show star (star (((B.primes X).piT u : 𝓞 B.fields.E) : B.fields.E)) *
      star (((B.primes X).piT u : 𝓞 B.fields.E) : B.fields.E) = ((B.primes X).T u : B.fields.E)
    rw [star_star]
    have h := congrArg (algebraMap (𝓞 B.fields.E) B.fields.E) ((base_fields_primes_ok B X).2.1.piT_norm u)
    rw [map_mul, map_natCast] at h
    exact h
  N_til b p x := by
    have hPr := (base_fields_primes_ok B X).2.1
    show x ∈ ((I.perIn u a).til b p).1.1.deco.1.N ↔ _
    rw [til_deco h u a b p]
    exact tilH_N _ p.1.1.deco (conj_piT_notMem hPr u) (piT_notMem_vGs hPr u) x
  f_til b p P x hx := by
    have hPr := (base_fields_primes_ok B X).2.1
    change x ∈ ((I.perIn u a).til b p).1.1.deco.1.N at hx
    show ((I.perIn u a).til b p).1.1.deco.1.f P x = _
    rw [til_deco h u a b p] at hx ⊢
    exact tilH_f _ p.1.1.deco (conj_piT_notMem hPr u) (piT_notMem_vGs hPr u) P x hx }

theorem perIn_laws : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok →
    ∀ u a, (I.perIn u a).Ok ∧ (I.perIn u a).Over (I.atIn u a) :=
  fun _ h u a => ⟨perIn_ok h u a, perIn_over h u a⟩

end GlobalTheory.Mem.Col2.PerLaw

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.LevelLaw

theorem ok_reRep {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {S : GStep E K n}
    {ST : Finset (HeightOneSpectrum (𝓞 E))} {A : TDat S ST} {T : ℕ} (pref : ∀ b, S.D b → Prop) (h : A.Ok T) :
    TDat.Ok (S := S.reRep pref) { A with } T :=
  { h with }

theorem tied_reRep {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n}
    {ST : Finset (HeightOneSpectrum (𝓞 E))} {A : TDat S ST} {T : ℕ} (pref : ∀ b, S.D b → Prop) (h : A.Tied T) :
    TDat.Tied (S := S.reRep pref) { A with } T :=
  { h with }

theorem atIn_ok : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ u a, (I.atIn u a).Ok := by
  intro B X I h u a
  obtain ⟨hX, hPr, -, -, hbig⟩ := base_fields_primes_ok B X
  have hQ : ∀ w ∈ I.Q a, ((B.primes X).T u : 𝓞 B.fields.E) ∉ w.asIdeal :=
    T_notMem_QE I.sel (I.tup a) u hPr h.sel_ok (h.T_mem u)
  exact
    { T_prime := hPr.T_prime u
      card_ST := (hPr.vT_card u).trans B.fields_f
      card_res := fun P => (card_res P.1).trans (hPr.vT_norm u P.1 P.2)
      lev := fun j => ok_reRep (I.pref u a j) (tdatAt_ok I.sel (I.tup a) (I.cst a) (I.idx a) (I.Tp a) hX hPr u j)
      tied := fun j => tied_reRep (I.pref u a j) (tdatAt_tied I.sel (I.tup a) (I.cst a) (I.idx a) (I.Tp a) hX hPr u hQ j)
      psi_ne := fun P => psiWeil_ne_one (xiUnitAt_vT B X u P).2
      free0 := stepAt_zero_free I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (I.Tp a) u hX hPr hbig (h.idx_ok a).zero_G
      duStar_pos := B.duStar_pos u
      Dstar_pos := B.Dstar_pos
      one_lt_gammaP := B.one_lt_gammaP }

end GlobalTheory.Mem.Col2.LevelLaw
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.FormSym

theorem mem_FiC_comp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    {ι : Type} [Fintype ι] (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (lam : ι → DomWeight n)
    {c c' : Type} (yc : c → UPts σ J (FiniteAdeleRing (𝓞 F) F)) (e : c' → c) (he : Function.Surjective e)
    (g : c → Frames (gramC J emb) → ℂ) :
    g ∘ e ∈ FiC S emb lam (yc ∘ e) ↔ g ∈ FiC S emb lam yc := by
  simp only [FiC, Submodule.mem_map]
  constructor
  · rintro ⟨h, hh, he'⟩
    refine ⟨h, hh, ?_⟩
    funext x
    obtain ⟨x', rfl⟩ := he x
    exact congrFun he' x'
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, rfl⟩

section Gen

variable {D : D7} {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m} {Ch : Type} {chOf : (D.mem u).C.cls i → Ch}

def clsOfChart (β : Ch) (hβ : ∀ c, chOf c = β)
    (K : LevelChart D (D.mem u).A.T (badG D) i hi (fun c : {c // chOf c = β} => (D.mem u).C.stab i c.1)
      (fun c => clsCrd D u i hi c.1)) : ClsTied u i hi where
  lev := K.lev
  y c := K.y ⟨c, hβ c⟩
  y_bij := K.y_bij.comp (f := fun c : (D.mem u).C.cls i => (⟨c, hβ c⟩ : {c // chOf c = β}))
    ⟨fun _ _ h => congrArg Subtype.val h, fun c => ⟨c.1, rfl⟩⟩
  y_lat c := K.y_lat ⟨c, hβ c⟩
  stabI c := K.stabI ⟨c, hβ c⟩
  stabI_inj c := K.stabI_inj ⟨c, hβ c⟩
  stabI_range c := K.stabI_range ⟨c, hβ c⟩



def valOfG [Subsingleton Ch] (eV : (D.mem u).A.vT ≃ PlT D u)
    (K : ∀ β : Ch, LevelChart D (D.mem u).A.T (badG D) i hi (fun c : {c // chOf c = β} => (D.mem u).C.stab i c.1)
      (fun c => clsCrd D u i hi c.1)) (β : Ch) (hβ : ∀ c, chOf c = β)
    (eY : (D.mem u).C.Y i ≃ Fr D i hi)
    (hde : ∃ C : GL (Fin (D.R.N i)) D.host.E,
      cT (sigD D : D.host.E →+* D.host.E) C.1 * C.1 = gramN D i hi ∧
      (∀ x : Fin (D.R.N i) → D.host.E, x ∈ selfDualLatticeCoords D i hi ↔ ∀ a, (C.1 *ᵥ x) a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) ∧
      ∀ τ z, (D.mem u).C.de i z τ = embT D τ C.1.det * ((eY z).1 τ).det)
    (hV : ValuationCompatibleChart (D.fm u) eY (fun _ => True) chOf (lat := fun c => clsCrd D u i hi c) K)
    (hI : IpVTieG (D.fm u) eY)
    (hD : DilationCompatibleChart (D.fm u) eY eV chOf (lat := fun c => clsCrd D u i hi c) K) :
    ValTied u eV i hi (clsOfChart β hβ (K β)) where
  eY := eY
  de := hde
  Fi φ := by
    rw [hV.Fi φ]
    constructor
    · intro h
      exact (mem_FiC_comp _ _ _ (K β).y (fun c => (⟨c, hβ c⟩ : {c // chOf c = β})) (fun c => ⟨c.1, rfl⟩) _).2 (h β)
    · intro h β'
      obtain rfl : β = β' := Subsingleton.elim _ _
      exact (mem_FiC_comp _ _ _ (K β).y (fun c => (⟨c, hβ c⟩ : {c // chOf c = β})) (fun c => ⟨c.1, rfl⟩) _).1 h
  ipV := hI
  rat := hV.rat
  lat x := by
    constructor
    · intro hx w
      exact (hV.lat w trivial x).1 (Submodule.subset_span hx)
    · intro h
      exact GlobalTheory.LvT.mem_of_forall_locW D _ (fun w => (hV.lat w trivial x).2 (h w))
  dil v a k hk c δ hδ := hD.dil v a k hk β ⟨c, hβ c⟩ δ hδ
  dilT v a k hk c δ hδ g hg := hD.dilT v a k hk β ⟨c, hβ c⟩ δ hδ g hg



def lvOfG (A : AtTTied u) (L : LevelCompatibleLattices (D.fm u) (D.mem u).A.T A.res i hi (fun c => clsCrd D u i hi c)) :
    LvTied u A i hi where
  pr := L.pr
  pr_surj := L.pr_surj
  pr_smul := L.pr_smul
  pr_ker := L.pr_ker
  fv_ker := L.fv_ker
  prk := L.prk
  prk_surj := L.prk_surj
  prk_smul := L.prk_smul
  prk_ker := L.prk_ker
  te := L.te

variable (A : AtTTied u) (L : LevelCompatibleLattices (D.fm u) (D.mem u).A.T A.res i hi (fun c => clsCrd D u i hi c))
  (K : ∀ β : Ch, LevelChart D (D.mem u).A.T (badG D) i hi (fun c : {c // chOf c = β} => (D.mem u).C.stab i c.1)
      (fun c => clsCrd D u i hi c.1)) (β : Ch) (hβ : ∀ c, chOf c = β)


theorem fvOfG (fMe : ∀ β v, (K β).lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v) (h : FvTieG L A.eV K fMe) :
    FvTie (lvOfG A L) (clsOfChart β hβ (K β)) (fMe β) :=
  fun v c z hz => h v β ⟨c, hβ c⟩ z hz


theorem upOfG (eY : (D.mem u).C.Y i ≃ Fr D i hi) (W : ValTied u A.eV i hi (clsOfChart β hβ (K β))) (hY : W.eY = eY)
    (h : UpNatTieG L eY A.eV K) : UpNatTie (lvOfG A L) (clsOfChart β hβ (K β)) W := by
  intro v c z hz
  obtain ⟨_, γ, η, κ, h1, h2, h3, h4, h5, h6⟩ := h v β ⟨c, hβ c⟩ z hz
  refine ⟨γ, η, κ, h1, h2, h3, h4, h5, fun g s s' hs => ?_⟩
  rw [hY] at hs
  exact h6 g s s' hs


theorem dnOfG (eY : (D.mem u).C.Y i ≃ Fr D i hi) (W : ValTied u A.eV i hi (clsOfChart β hβ (K β))) (hY : W.eY = eY)
    (h : DnNatTieG L eY A.eV K) : DnNatTie (lvOfG A L) (clsOfChart β hβ (K β)) W := by
  intro v c g hg
  obtain ⟨_, γ, η, κ, h1, h2, h3, h4, h6⟩ := h v β ⟨c, hβ c⟩ g hg
  refine ⟨γ, η, κ, h1, h2, h3, h4, fun f s s' hs => ?_⟩
  rw [hY] at hs
  exact h6 f s s' hs

end Gen

section Gen2

variable {D : D7} {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m}


theorem normOfG {eV : (D.mem u).A.vT ≃ PlT D u} {K : ClsTied u i hi} (eY : (D.mem u).C.Y i ≃ Fr D i hi)
    (W : ValTied u eV i hi K) (hY : W.eY = eY) (h : NormTieG (D.fm u) eY) : NormTie W := by
  intro s x Pc hPc o ho
  rw [hY] at hPc
  exact h s x Pc hPc o ho


theorem bwOfG (A : AtTTied u) {K : ClsTied u i hi} (eY : (D.mem u).C.Y i ≃ Fr D i hi)
    (W : ValTied u A.eV i hi K) (hY : W.eY = eY)
    (h : BwTieG (D.fm u) (D.mem u).A.T A.res eY (fun c => clsCrd D u i hi c)) : BwTie A W := by
  intro w hw hs v x
  rw [hY]
  exact h w hw hs v x

end Gen2



theorem readsK_one {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {u : B.Word} {a : I.ι}
    {i : ℕ} {hi : i ≤ B.R.m} {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {Ch : Type} {chOf : (I.stp u a i).Cl → Ch}
    {K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
      (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))} (h : I.ReadsK l Z u a i hi chOf K) (β : Ch)
    (hβ : ∀ c, chOf c = β) :
    ∃ k, I.Reads u a i (fun _ => ()) (fun _ => (K β).lev.Lb) (fun _ => (K β).lev.U) (fun _ => (K β).lev.chi)
      (fun c => ((K β).y ⟨c, hβ c⟩).1) (fun c s => ((K β).stabI ⟨c, hβ c⟩ s).1) k := by
  obtain rfl : chOf = fun _ => β := funext hβ
  obtain ⟨k, hk⟩ := h
  refine ⟨fun _ => k β, ⟨fun c c' => ⟨fun _ => (hk.key c c').1 rfl, fun _ => rfl⟩, fun _ => ?_, fun _ => hk.lb β,
    fun _ => hk.k_std β, fun _ => hk.k_off β, fun _ => hk.k_T β, hk.pt, hk.lev, hk.chr, hk.stab⟩⟩
  obtain ⟨c, _⟩ := hk.onto β
  exact ⟨c, rfl⟩

end GlobalTheory.Mem.FormSym

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ChTw

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

def LocMv (u : B.Word) (a : I.ι) (i : ℕ) (c : (I.stp u a i).Cl) (s : GA B (B.R.N i)) (κ : (I.stp u a i).G c.1) : Prop :=
  (I.stp u a i).gam c.1 κ = 1 ∧
    cosetIn ((I.stp u a i).act c.1 κ ((I.stp u a i).rep c)) = cosetIn ((I.stp u a i).rep c) ∧
    ∀ g : GA B (B.R.N i), PtOf g ((I.stp u a i).rep c).1.1 → PtOf (g * s) ((I.stp u a i).act c.1 κ ((I.stp u a i).rep c)).1.1

theorem reads_of_locMv (hI : I.Ok) {u : B.Word} {a : I.ι} {i : ℕ} {Ch : Type} {chOf : (I.stp u a i).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)} {U : Ch → Subgroup (GA B (B.R.N i))} {chi : ∀ β, U β →* ℂˣ}
    {y : (I.stp u a i).Cl → GA B (B.R.N i)} {st : ∀ c, (I.stp u a i).Stab c → GL (Fin (B.R.N i)) B.host.E}
    {k : Ch → GA B (B.R.N i)} (hR : I.Reads u a i chOf Lb U chi y st k) (c : (I.stp u a i).Cl) (x : GA B (B.R.N i))
    (κ : (I.stp u a i).G c.1) (h : LocMv I u a i c ((k (chOf c))⁻¹ * x * k (chOf c)) κ) :
    ∃ hx : x ∈ U (chOf c), ((chi (chOf c) ⟨x, hx⟩ : ℂˣ) : ℂ) = B.embLL (((I.stp u a i).chr c.1 κ : B.LLˣ) : B.LL) := by
  have hd : Disjoint (B.primes X).vGs (I.Q a) :=
    Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I a) (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).2.1
  have hp : PtOf (y c * k (chOf c)) ((I.stp u a i).rep c).1.1 :=
    IsPtOf.of_extTo (ColIn.Q_subset_SQ I a) hd (hR.pt c)
  have e : y c * k (chOf c) * ((k (chOf c))⁻¹ * x * k (chOf c)) = y c * x * k (chOf c) := by group
  have hq := h.2.2 _ hp
  rw [e] at hq
  have hx : x ∈ U (chOf c) := (hR.lev c x _ hq).2 ⟨κ, h.1, rfl, h.2.1⟩
  exact ⟨hx, hR.chr c ⟨x, hx⟩ κ h.1 hq⟩

end GlobalTheory.Mem.Col2.TC.ChTw
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

theorem underQ_notMem {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι)
    (v : HeightOneSpectrum (𝓞 B.host.F)) (hv : I.UnderQ a v) :
    ((B.T u : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal ∧ ∀ j, ((B.host.g j : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal := by
  obtain ⟨P, hP, rfl⟩ := hv
  have key : ∀ p : ℕ, p.Prime → p ∈ I.S → ((p : ℕ) : 𝓞 B.host.F) ∉ (P.under (𝓞 B.host.F)).asIdeal := by
    intro p hp hS hm
    apply GlobalTheory.KFormsCmp.notMem_of_QE hI.sel_ok (I.tup a) hP hp hS
    have := Ideal.mem_comap.1 hm
    simpa using this
  exact ⟨key _ (l.pr.T_prime u) (hI.T_mem u), fun j => key _ (l.pr.g_prime j) (hI.g_mem j)⟩

theorem underQ_prime_to_bad : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → I.Laws → ∀ (u : B.Word) (a : I.ι)
    (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v →
    ((B.T u : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal ∧ ∀ j, ((B.host.g j : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal :=
  fun I hI l u a v hv => underQ_notMem I hI l u a v hv

end GlobalTheory.Mem.Col2.TC
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IntegralityCompare

namespace GlobalTheory.IntegralityCompare

theorem weight_arith_step : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (μ : I.ι) (i : ℕ), i < B.R.m →
    ∃ k : (I.rec7 l Z).what₂.Tau → ℕ,
      (∀ τ, (k τ : ℤ) = shiftOf (lamTG (I.fm l u μ) i) τ + ((I.rec7 l Z).chTw u μ).sSharp i τ) ∧
      ∀ τ r, nuT (I.rec7 l Z) u i τ r = ((I.fm l u μ).lam i τ).natW r + k τ := by
  intro B X I hOk hPins l Z u μ i hi
  obtain ⟨n, h1, h2, -, -⟩ := GlobalTheory.KerWtStep.trueWt_step (I.rec7 l Z) u _ _ _ (I.fm l u μ) i hi
  refine ⟨n, fun τ => ?_, fun τ r => ?_⟩
  · rw [← h2 τ]; rfl
  · rw [← h1 τ r]
    unfold lamTG
    rw [natW_shW]
    rfl

end GlobalTheory.IntegralityCompare
end
