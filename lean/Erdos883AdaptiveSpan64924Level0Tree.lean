import Erdos883AdaptiveSpan64924Level0TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength64924_0 : adaptiveNumericSpans64924_0.length = 567 := by decide +kernel
theorem adaptiveSpanEvenCache64924_0 : adaptiveSpanEven64924_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain64924_0 : adaptiveSpanEven64924_0.domainCheck 32462 = true := by decide +kernel
theorem adaptiveSpanEvenEntries64924_0 : adaptiveSpanEven64924_0.spans = coreEvenSpans 32462 0 adaptiveNumericSpans64924_0 := by
  decide +kernel
theorem adaptiveSpanWholeCache64924_0 : adaptiveSpanWhole64924_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain64924_0 : adaptiveSpanWhole64924_0.domainCheck 32462 = true := by decide +kernel
theorem adaptiveSpanWholeEntries64924_0 : adaptiveSpanWhole64924_0.spans = coreWholeSpans 0 adaptiveNumericSpans64924_0 := by
  decide +kernel
end Erdos883Verified
