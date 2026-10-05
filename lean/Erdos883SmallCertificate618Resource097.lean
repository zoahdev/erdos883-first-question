import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_97 :
    (List.ofFn coreChunks618_97).flatten =
      (coreData618.take (coreResources618 97).q).drop 235 := by
  decide +kernel

theorem coreCheck618_97 :
    ∀ c : Fin 1, (coreChunks618_97 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 97)) = true := by
  decide +kernel
#print axioms coreFlatten618_97
#print axioms coreCheck618_97
end Erdos883Verified
