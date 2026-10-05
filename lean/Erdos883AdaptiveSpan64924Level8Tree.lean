import Erdos883AdaptiveSpan64924Level8TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength64924_8 : adaptiveNumericSpans64924_8.length = 569 := by decide +kernel
theorem adaptiveSpanEvenCache64924_8 : adaptiveSpanEven64924_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain64924_8 : adaptiveSpanEven64924_8.domainCheck 32462 = true := by decide +kernel
theorem adaptiveSpanEvenEntries64924_8 : adaptiveSpanEven64924_8.spans = coreEvenSpans 32462 0 adaptiveNumericSpans64924_8 := by
  decide +kernel
theorem adaptiveSpanWholeCache64924_8 : adaptiveSpanWhole64924_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain64924_8 : adaptiveSpanWhole64924_8.domainCheck 32462 = true := by decide +kernel
theorem adaptiveSpanWholeEntries64924_8 : adaptiveSpanWhole64924_8.spans = coreWholeSpans 0 adaptiveNumericSpans64924_8 := by
  decide +kernel
end Erdos883Verified
