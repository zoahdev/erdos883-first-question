import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_72 :
    (List.ofFn coreChunks618_72).flatten =
      (coreData618.take (coreResources618 72).q).drop 140 := by
  decide +kernel

theorem coreCheck618_72 :
    ∀ c : Fin 1, (coreChunks618_72 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 72)) = true := by
  decide +kernel
#print axioms coreFlatten618_72
#print axioms coreCheck618_72
end Erdos883Verified
