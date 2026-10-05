import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_57 :
    (List.ofFn coreChunks618_57).flatten =
      (coreData618.take (coreResources618 57).q).drop 116 := by
  decide +kernel

theorem coreCheck618_57 :
    ∀ c : Fin 1, (coreChunks618_57 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 57)) = true := by
  decide +kernel
#print axioms coreFlatten618_57
#print axioms coreCheck618_57
end Erdos883Verified
