import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_77 :
    (List.ofFn coreChunks618_77).flatten =
      (coreData618.take (coreResources618 77).q).drop 152 := by
  decide +kernel

theorem coreCheck618_77 :
    ∀ c : Fin 1, (coreChunks618_77 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 77)) = true := by
  decide +kernel
#print axioms coreFlatten618_77
#print axioms coreCheck618_77
end Erdos883Verified
