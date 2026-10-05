import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_84 :
    (List.ofFn coreChunks618_84).flatten =
      (coreData618.take (coreResources618 84).q).drop 171 := by
  decide +kernel

theorem coreCheck618_84 :
    ∀ c : Fin 1, (coreChunks618_84 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 84)) = true := by
  decide +kernel
#print axioms coreFlatten618_84
#print axioms coreCheck618_84
end Erdos883Verified
