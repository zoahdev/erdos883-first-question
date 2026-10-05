import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_87 :
    (List.ofFn coreChunks618_87).flatten =
      (coreData618.take (coreResources618 87).q).drop 182 := by
  decide +kernel

theorem coreCheck618_87 :
    ∀ c : Fin 1, (coreChunks618_87 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 87)) = true := by
  decide +kernel
#print axioms coreFlatten618_87
#print axioms coreCheck618_87
end Erdos883Verified
