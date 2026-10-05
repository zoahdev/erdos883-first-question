import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_95 :
    (List.ofFn coreChunks618_95).flatten =
      (coreData618.take (coreResources618 95).q).drop 208 := by
  decide +kernel

theorem coreCheck618_95 :
    ∀ c : Fin 1, (coreChunks618_95 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 95)) = true := by
  decide +kernel
#print axioms coreFlatten618_95
#print axioms coreCheck618_95
end Erdos883Verified
