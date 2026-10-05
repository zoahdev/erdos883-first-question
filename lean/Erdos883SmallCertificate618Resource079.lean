import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_79 :
    (List.ofFn coreChunks618_79).flatten =
      (coreData618.take (coreResources618 79).q).drop 157 := by
  decide +kernel

theorem coreCheck618_79 :
    ∀ c : Fin 1, (coreChunks618_79 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 79)) = true := by
  decide +kernel
#print axioms coreFlatten618_79
#print axioms coreCheck618_79
end Erdos883Verified
