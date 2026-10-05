import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_28 :
    (List.ofFn coreChunks618_28).flatten =
      (coreData618.take (coreResources618 28).q).drop 139 := by
  decide +kernel

theorem coreCheck618_28 :
    ∀ c : Fin 1, (coreChunks618_28 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 28)) = true := by
  decide +kernel
#print axioms coreFlatten618_28
#print axioms coreCheck618_28
end Erdos883Verified
