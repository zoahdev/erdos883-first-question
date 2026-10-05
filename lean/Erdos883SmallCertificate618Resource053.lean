import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_53 :
    (List.ofFn coreChunks618_53).flatten =
      (coreData618.take (coreResources618 53).q).drop 109 := by
  decide +kernel

theorem coreCheck618_53 :
    ∀ c : Fin 1, (coreChunks618_53 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 53)) = true := by
  decide +kernel
#print axioms coreFlatten618_53
#print axioms coreCheck618_53
end Erdos883Verified
