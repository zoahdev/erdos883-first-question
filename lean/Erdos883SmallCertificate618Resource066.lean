import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_66 :
    (List.ofFn coreChunks618_66).flatten =
      (coreData618.take (coreResources618 66).q).drop 133 := by
  decide +kernel

theorem coreCheck618_66 :
    ∀ c : Fin 1, (coreChunks618_66 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 66)) = true := by
  decide +kernel
#print axioms coreFlatten618_66
#print axioms coreCheck618_66
end Erdos883Verified
