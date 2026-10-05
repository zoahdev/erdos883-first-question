import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_3 :
    (List.ofFn coreChunks618_3).flatten =
      (coreData618.take (coreResources618 3).q).drop 72 := by
  decide +kernel

theorem coreCheck618_3 :
    ∀ c : Fin 1, (coreChunks618_3 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 3)) = true := by
  decide +kernel
#print axioms coreFlatten618_3
#print axioms coreCheck618_3
end Erdos883Verified
