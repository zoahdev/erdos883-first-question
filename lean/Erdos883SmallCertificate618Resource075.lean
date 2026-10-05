import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_75 :
    (List.ofFn coreChunks618_75).flatten =
      (coreData618.take (coreResources618 75).q).drop 148 := by
  decide +kernel

theorem coreCheck618_75 :
    ∀ c : Fin 1, (coreChunks618_75 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 75)) = true := by
  decide +kernel
#print axioms coreFlatten618_75
#print axioms coreCheck618_75
end Erdos883Verified
