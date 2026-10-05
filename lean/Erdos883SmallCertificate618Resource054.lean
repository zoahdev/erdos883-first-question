import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_54 :
    (List.ofFn coreChunks618_54).flatten =
      (coreData618.take (coreResources618 54).q).drop 111 := by
  decide +kernel

theorem coreCheck618_54 :
    ∀ c : Fin 1, (coreChunks618_54 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 54)) = true := by
  decide +kernel
#print axioms coreFlatten618_54
#print axioms coreCheck618_54
end Erdos883Verified
