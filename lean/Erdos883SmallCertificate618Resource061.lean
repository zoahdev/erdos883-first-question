import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_61 :
    (List.ofFn coreChunks618_61).flatten =
      (coreData618.take (coreResources618 61).q).drop 124 := by
  decide +kernel

theorem coreCheck618_61 :
    ∀ c : Fin 1, (coreChunks618_61 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 61)) = true := by
  decide +kernel
#print axioms coreFlatten618_61
#print axioms coreCheck618_61
end Erdos883Verified
