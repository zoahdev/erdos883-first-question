import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_58 :
    (List.ofFn coreChunks618_58).flatten =
      (coreData618.take (coreResources618 58).q).drop 119 := by
  decide +kernel

theorem coreCheck618_58 :
    ∀ c : Fin 1, (coreChunks618_58 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 58)) = true := by
  decide +kernel
#print axioms coreFlatten618_58
#print axioms coreCheck618_58
end Erdos883Verified
