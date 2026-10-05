import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_68 :
    (List.ofFn coreChunks618_68).flatten =
      (coreData618.take (coreResources618 68).q).drop 136 := by
  decide +kernel

theorem coreCheck618_68 :
    ∀ c : Fin 1, (coreChunks618_68 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 68)) = true := by
  decide +kernel
#print axioms coreFlatten618_68
#print axioms coreCheck618_68
end Erdos883Verified
