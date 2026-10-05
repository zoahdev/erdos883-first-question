import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_104 :
    (List.ofFn coreChunks618_104).flatten =
      (coreData618.take (coreResources618 104).q).drop 266 := by
  decide +kernel

theorem coreCheck618_104 :
    ∀ c : Fin 1, (coreChunks618_104 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 104)) = true := by
  decide +kernel
#print axioms coreFlatten618_104
#print axioms coreCheck618_104
end Erdos883Verified
