import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_44 :
    (List.ofFn coreChunks618_44).flatten =
      (coreData618.take (coreResources618 44).q).drop 98 := by
  decide +kernel

theorem coreCheck618_44 :
    ∀ c : Fin 1, (coreChunks618_44 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 44)) = true := by
  decide +kernel
#print axioms coreFlatten618_44
#print axioms coreCheck618_44
end Erdos883Verified
