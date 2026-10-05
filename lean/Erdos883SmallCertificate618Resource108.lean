import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_108 :
    (List.ofFn coreChunks618_108).flatten =
      (coreData618.take (coreResources618 108).q).drop 197 := by
  decide +kernel

theorem coreCheck618_108 :
    ∀ c : Fin 1, (coreChunks618_108 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 108)) = true := by
  decide +kernel
#print axioms coreFlatten618_108
#print axioms coreCheck618_108
end Erdos883Verified
