import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_49 :
    (List.ofFn coreChunks618_49).flatten =
      (coreData618.take (coreResources618 49).q).drop 103 := by
  decide +kernel

theorem coreCheck618_49 :
    ∀ c : Fin 1, (coreChunks618_49 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 49)) = true := by
  decide +kernel
#print axioms coreFlatten618_49
#print axioms coreCheck618_49
end Erdos883Verified
