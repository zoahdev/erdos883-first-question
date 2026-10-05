import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_55 :
    (List.ofFn coreChunks618_55).flatten =
      (coreData618.take (coreResources618 55).q).drop 113 := by
  decide +kernel

theorem coreCheck618_55 :
    ∀ c : Fin 1, (coreChunks618_55 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 55)) = true := by
  decide +kernel
#print axioms coreFlatten618_55
#print axioms coreCheck618_55
end Erdos883Verified
