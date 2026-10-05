import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_67 :
    (List.ofFn coreChunks618_67).flatten =
      (coreData618.take (coreResources618 67).q).drop 134 := by
  decide +kernel

theorem coreCheck618_67 :
    ∀ c : Fin 1, (coreChunks618_67 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 67)) = true := by
  decide +kernel
#print axioms coreFlatten618_67
#print axioms coreCheck618_67
end Erdos883Verified
