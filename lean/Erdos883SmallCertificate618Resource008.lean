import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_8 :
    (List.ofFn coreChunks618_8).flatten =
      (coreData618.take (coreResources618 8).q).drop 113 := by
  decide +kernel

theorem coreCheck618_8 :
    ∀ c : Fin 1, (coreChunks618_8 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 8)) = true := by
  decide +kernel
#print axioms coreFlatten618_8
#print axioms coreCheck618_8
end Erdos883Verified
