import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_42 :
    (List.ofFn coreChunks618_42).flatten =
      (coreData618.take (coreResources618 42).q).drop 95 := by
  decide +kernel

theorem coreCheck618_42 :
    ∀ c : Fin 1, (coreChunks618_42 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 42)) = true := by
  decide +kernel
#print axioms coreFlatten618_42
#print axioms coreCheck618_42
end Erdos883Verified
