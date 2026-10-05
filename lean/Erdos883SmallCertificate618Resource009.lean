import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_9 :
    (List.ofFn coreChunks618_9).flatten =
      (coreData618.take (coreResources618 9).q).drop 115 := by
  decide +kernel

theorem coreCheck618_9 :
    ∀ c : Fin 1, (coreChunks618_9 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 9)) = true := by
  decide +kernel
#print axioms coreFlatten618_9
#print axioms coreCheck618_9
end Erdos883Verified
