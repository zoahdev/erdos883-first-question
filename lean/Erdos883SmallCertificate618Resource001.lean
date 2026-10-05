import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_1 :
    (List.ofFn coreChunks618_1).flatten =
      (coreData618.take (coreResources618 1).q).drop 54 := by
  decide +kernel

theorem coreCheck618_1 :
    ∀ c : Fin 1, (coreChunks618_1 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 1)) = true := by
  decide +kernel
#print axioms coreFlatten618_1
#print axioms coreCheck618_1
end Erdos883Verified
