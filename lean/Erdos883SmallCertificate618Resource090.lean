import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_90 :
    (List.ofFn coreChunks618_90).flatten =
      (coreData618.take (coreResources618 90).q).drop 189 := by
  decide +kernel

theorem coreCheck618_90 :
    ∀ c : Fin 1, (coreChunks618_90 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 90)) = true := by
  decide +kernel
#print axioms coreFlatten618_90
#print axioms coreCheck618_90
end Erdos883Verified
