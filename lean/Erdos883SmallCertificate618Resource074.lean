import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_74 :
    (List.ofFn coreChunks618_74).flatten =
      (coreData618.take (coreResources618 74).q).drop 144 := by
  decide +kernel

theorem coreCheck618_74 :
    ∀ c : Fin 1, (coreChunks618_74 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 74)) = true := by
  decide +kernel
#print axioms coreFlatten618_74
#print axioms coreCheck618_74
end Erdos883Verified
